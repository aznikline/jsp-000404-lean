#!/usr/bin/env python3
"""One JSP heavy job: no shell, global lock, nice 15, sampled tree RSS.

Lean: --cwd REPO --log LOG -- lake env lean -j 2 -M 4096 FILE.lean
Solver: --solver-threads 1 --cwd REPO --log LOG -- python3 SCRIPT.py ARGS
Caller must configure every solver instance for one thread; this flag attests it.
No lake build is accepted. Self-test uses a fixed tiny Python sleep child only.
Thread limits do not cap total system CPU; RSS polling is not a hard allocation cap.
Calibrated imports: --mapped-rss-gib 6 permits RSS6GiB/footprint4GiB,
Lean -j1 only, memory-free55% preflight/45% running; API failure restores RSS4GiB.
"""
import argparse
import ctypes
import fcntl
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
HEAVY = {'lean', 'lake', 'z3', 'cvc4', 'cvc5', 'yices', 'yices-smt2',
         'mathsat', 'gurobi', 'gurobi_cl', 'scip', 'cadical', 'kissat', 'solver'}


class RUsageV0(ctypes.Structure):
    # Local macOS SDK sys/resource.h:202-214; size=96, fields in bytes.
    _fields_ = [('uuid', ctypes.c_uint8 * 16)] + [(n, ctypes.c_uint64) for n in
        ('user_time', 'system_time', 'pkg_idle_wkups', 'interrupt_wkups', 'pageins',
         'wired_size', 'resident_size', 'phys_footprint', 'proc_start_abstime', 'proc_exit_abstime')]


def process_memory(pid):
    try:
        lib = ctypes.CDLL('/usr/lib/libproc.dylib', use_errno=True)
        lib.proc_pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
        lib.proc_pid_rusage.restype = ctypes.c_int
        usage = RUsageV0()
        if lib.proc_pid_rusage(pid, 0, ctypes.byref(usage)) != 0:
            return {'rusage_error': ctypes.get_errno()}
        return {'resident_bytes': usage.resident_size, 'footprint_bytes': usage.phys_footprint}
    except (OSError, AttributeError) as exc:
        return {'rusage_error': str(exc)}


def sample_process_memory(rows):
    measured = [dict(r, **process_memory(r['pid'])) for r in rows]
    missing = [r for r in measured if 'resident_bytes' not in r]
    if not missing:
        return measured, []
    still_present = {r['pid'] for r in snapshot()}
    diagnostics = [dict(r, gone=r['pid'] not in still_present) for r in missing]
    gone = {r['pid'] for r in diagnostics if r['gone']}
    return [r for r in measured if r['pid'] not in gone], diagnostics


def snapshot():
    raw = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,pgid=,rss=,stat=,comm='], text=True)
    rows = []
    for line in raw.splitlines():
        p = line.strip().split(None, 5)
        if len(p) == 6:
            rows.append(dict(pid=int(p[0]), ppid=int(p[1]), pgid=int(p[2]),
                             rss_kib=int(p[3]), stat=p[4], comm=p[5]))
    return rows


def memory_free():
    raw = subprocess.check_output(['memory_pressure'], text=True, timeout=5)
    hit = re.search(r'System-wide memory free percentage:\s*(\d+)%', raw)
    if not hit:
        raise RuntimeError('cannot read macOS memory pressure')
    return int(hit.group(1))


def validate(args, cmd):
    if args.self_test is not None:
        if cmd:
            raise ValueError('self-test cannot take a command')
        return [sys.executable, '-c', 'import time; time.sleep(float(__import__("sys").argv[1]))',
                str(args.self_test)]
    if not cmd:
        raise ValueError('explicit command argv is required after --')
    name = Path(cmd[0]).name
    if name == 'lake':
        tail = cmd[3:]
        if cmd[1:3] != ['env', 'lean']:
            raise ValueError('only lake env lean is allowed; lake build is rejected')
    elif name == 'lean':
        tail = cmd[1:]
    elif name in {'python3', 'python', 'z3', 'cvc5', 'yices-smt2'}:
        if args.solver_threads != 1:
            raise ValueError('solver caller must attest --solver-threads 1')
        if name.startswith('python') and (len(cmd) < 2 or not cmd[1].endswith('.py')):
            raise ValueError('Python solver requires an explicit .py file, not -c or -m')
        return cmd
    else:
        raise ValueError('unsupported command; no shell or wrapper commands')
    threads = re.findall(r'(?:^|\s)(?:-j\s*|--threads[=\s]+)(\d+)(?=\s|$)', ' '.join(tail))
    if len(threads) != 1 or not 1 <= int(threads[0]) <= 2:
        raise ValueError('Lean requires exactly one -j 1 or -j 2 option')
    if args.mapped_rss_gib is not None and int(threads[0]) != 1:
        raise ValueError('calibrated mapped-RSS mode requires Lean -j 1')
    memory = re.findall(r'(?:^|\s)(?:-M\s*|--memory[=\s]+)(\d+)(?=\s|$)', ' '.join(tail))
    if len(memory) != 1 or not 1 <= int(memory[0]) <= 4096:
        raise ValueError('Lean requires exactly one -M 4096 or smaller memory option')
    if not any(x.endswith('.lean') for x in tail) or '--run' in tail:
        raise ValueError('Lean must check an explicit .lean file; --run is rejected')
    return cmd


def stop_owned(child):
    for sig, grace in [(signal.SIGTERM, 1.0), (signal.SIGKILL, .3)]:
        child.poll()  # Reap exited leader before inspecting its process group.
        if not any(r['pgid'] == child.pid and 'Z' not in r['stat'] for r in snapshot()):
            break
        try:
            os.killpg(child.pid, sig)
        except ProcessLookupError:
            break
        deadline = time.monotonic() + grace
        while time.monotonic() < deadline:
            child.poll()
            if not any(r['pgid'] == child.pid and 'Z' not in r['stat'] for r in snapshot()):
                break
            time.sleep(.05)
    child.wait(timeout=2)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--cwd', default=os.getcwd())
    parser.add_argument('--log', required=True, help='raw stdout/stderr; adjacent .json records outcome')
    parser.add_argument('--rss-gib', type=float, default=4.0)
    parser.add_argument('--mapped-rss-gib', type=float, help='opt-in Lean -j1 RSS limit, >4 and <=6; footprint stays <=4 GiB')
    parser.add_argument('--wall', type=float, default=180.0)
    parser.add_argument('--solver-threads', type=int)
    parser.add_argument('--self-test', type=float, metavar='SLEEP_SECONDS')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    log = Path(args.log).resolve()
    result = dict(status='ERROR', argv=[], cwd=str(Path(args.cwd).resolve()),
                  rss_cap_gib=args.rss_gib, wall_cap_s=args.wall, nice=15,
                  mapped_rss_requested_gib=args.mapped_rss_gib, footprint_cap_gib=None,
                  preflight_free_min_percent=55 if args.mapped_rss_gib else 25,
                  running_free_min_percent=45 if args.mapped_rss_gib else 25,
                  max_rss_kib=0, max_resident_bytes=None, max_footprint_bytes=None,
                  rusage_flavor=0, rusage_struct_bytes=ctypes.sizeof(RUsageV0),
                  elapsed_s=0, child_exit=None)
    child = None
    started = time.monotonic()
    code = 70
    try:
        if not 0 < args.rss_gib <= 4 or not 0 < args.wall <= 180:
            raise ValueError('limits must be positive and at most 4 GiB / 180 seconds')
        if args.mapped_rss_gib is not None and not 4 < args.mapped_rss_gib <= 6:
            raise ValueError('calibrated mapped-RSS limit must be >4 and <=6 GiB')
        cmd = args.command[1:] if args.command[:1] == ['--'] else args.command
        if args.mapped_rss_gib and args.self_test is None and (not cmd or Path(cmd[0]).name not in {'lake', 'lean'}):
            raise ValueError('calibrated mapped-RSS mode is Lean-only; solver jobs are rejected')
        result['argv'] = validate(args, cmd)
        if args.mapped_rss_gib:
            result['footprint_cap_gib'] = 4.0
            if 'footprint_bytes' in process_memory(os.getpid()):
                result['rss_cap_gib'] = args.mapped_rss_gib
            else:
                result['mapped_rss_fallback'] = True
        log.parent.mkdir(parents=True, exist_ok=True)
        with (BASE / 'heavy.lock').open('a+') as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                result['status'], code = 'BUSY_LOCK', 75
                return code
            busy = [r for r in snapshot() if Path(r['comm']).name.lower() in HEAVY]
            if busy:
                result.update(status='BUSY_EXISTING', existing=busy)
                code = 75
                return code
            free = memory_free()
            result['preflight_free_percent'] = free
            if free < result['preflight_free_min_percent']:
                result['status'], code = 'LOW_MEMORY_PREFLIGHT', 75
                return code
            with log.open('wb') as output:
                child = subprocess.Popen(result['argv'], cwd=args.cwd, stdout=output,
                                         stderr=subprocess.STDOUT, start_new_session=True,
                                         preexec_fn=lambda: os.nice(15))
                result['child_pid'] = child.pid
                started = time.monotonic()
                last_pressure = started
                while child.poll() is None:
                    rows = snapshot()
                    owned = {child.pid} | {r['pid'] for r in rows if r['pgid'] == child.pid}
                    previous = set()
                    while owned != previous:
                        previous = set(owned)
                        owned |= {r['pid'] for r in rows if r['ppid'] in owned}
                    rss = sum(r['rss_kib'] for r in rows if r['pid'] in owned)
                    measured, missing = sample_process_memory([r for r in rows if r['pid'] in owned])
                    if missing:
                        result['rusage_missing_count'] = result.get('rusage_missing_count', 0) + len(missing)
                        events = result.setdefault('rusage_missing_rows', [])
                        events.extend(dict(r, elapsed_s=round(time.monotonic() - started, 3)) for r in missing[:max(0, 64 - len(events))])
                        gone = result.setdefault('rusage_gone_pids', [])
                        gone.extend(r['pid'] for r in missing if r['gone'] and r['pid'] not in gone and len(gone) < 64)
                    if all('resident_bytes' in r for r in measured):
                        for field in ('resident_bytes', 'footprint_bytes'):
                            result['max_' + field] = max(result['max_' + field] or 0, sum(r[field] for r in measured))
                    else:
                        result['rusage_incomplete'] = True
                        if args.mapped_rss_gib:
                            result['rss_cap_gib'] = args.rss_gib
                            result['mapped_rss_fallback'] = True
                    if rss >= result['max_rss_kib']:
                        result['processes_at_max_rss'] = measured
                    result['max_rss_kib'] = max(rss, result['max_rss_kib'])
                    elapsed = time.monotonic() - started
                    reason = 'RSS_LIMIT' if rss > result['rss_cap_gib'] * 1024 ** 2 else None
                    if args.mapped_rss_gib and all('footprint_bytes' in r for r in measured):
                        if sum(r['footprint_bytes'] for r in measured) > 4 * 1024 ** 3:
                            reason = 'FOOTPRINT_LIMIT'
                    if elapsed >= args.wall:
                        reason = 'WALL_LIMIT'
                    if time.monotonic() - last_pressure >= 5:
                        last_pressure = time.monotonic()
                        result['last_free_percent'] = memory_free()
                        if result['last_free_percent'] < result['running_free_min_percent']:
                            reason = 'LOW_MEMORY_RUNNING'
                    if reason:
                        result['status'], code = reason, 124
                        stop_owned(child)
                        break
                    time.sleep(min(.2, args.wall / 4))
                else:
                    result['status'] = 'OK' if child.returncode == 0 else 'CHILD_FAILED'
                    code = child.returncode if child.returncode >= 0 else 128 - child.returncode
                result['child_exit'] = child.returncode
    except BaseException as exc:
        result['error'] = str(exc)
        if isinstance(exc, KeyboardInterrupt):
            result['status'], code = 'INTERRUPTED', 130
        if child is not None and child.poll() is None:
            stop_owned(child)
    finally:
        result['elapsed_s'] = round(time.monotonic() - started, 3)
        result['exit_code'] = code
        log.parent.mkdir(parents=True, exist_ok=True)
        log.touch(exist_ok=True)
        record = json.dumps(result, ensure_ascii=False, indent=2)
        log.with_suffix(log.suffix + '.json').write_text(record + '\n')
        print(record)
    return code


if __name__ == '__main__':
    sys.exit(main())
