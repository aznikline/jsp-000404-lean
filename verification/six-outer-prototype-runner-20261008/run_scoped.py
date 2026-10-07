import sys, json, time, os, signal, subprocess, hashlib, re
from pathlib import Path
mode, module, tag = sys.argv[1:4]
initial_scan = subprocess.run(['ps', '-axo', 'comm='], capture_output=True, text=True)
initial_lean = [line for line in initial_scan.stdout.splitlines() if Path(line.strip()).name == 'lean']
if initial_lean:
    raise SystemExit('RESOURCE_NOT_ACQUIRED: another Lean is active')
src = Path(module.replace('.', '/') + '.lean')
out = Path('verification') / tag
out.mkdir(parents=True, exist_ok=True)
state = json.loads((out / 'runs.json').read_text()) if (out / 'runs.json').exists() else []
attempt = 1 + sum(r['mode'] == mode for r in state)
label = f'{mode}-attempt{attempt}'
source_hash = hashlib.sha256(src.read_bytes()).hexdigest()
snapshot = out / (label + '-source.lean')
snapshot.write_bytes(src.read_bytes())
cmd = ['lake', 'env', 'lean', '--trust=0', '-M8000', '-o', str(Path('.lake') / (tag + '-' + label + '.olean')), str(src)] if mode == 'strict' else ['lake', 'build', module]
log = out / (label + '.log')
t0 = time.monotonic()
peak_lean = 0
peak_tree = 0
cap_killed = False
wall_killed = False
parallel_killed = False
peak_global_lean_count = 0
wall_cap_seconds = 180
with log.open('wb') as f:
    proc = subprocess.Popen(['/usr/bin/time', '-l', *cmd], stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
    while proc.poll() is None:
        scan = subprocess.run(['ps', '-axo', 'pid=,ppid=,rss=,comm='], capture_output=True, text=True)
        rows = {}
        for row in scan.stdout.splitlines():
            parts = row.split(None, 3)
            if len(parts) == 4:
                try: rows[int(parts[0])] = (int(parts[1]), int(parts[2]), parts[3])
                except ValueError: pass
        global_lean_count = sum(Path(row[2]).name == 'lean' for row in rows.values())
        peak_global_lean_count = max(peak_global_lean_count, global_lean_count)
        if global_lean_count > 1: parallel_killed = True
        descendants = {proc.pid}
        change = True
        while change:
            change = False
            for pid, (ppid, rss, comm) in rows.items():
                if ppid in descendants and pid not in descendants:
                    descendants.add(pid); change = True
        rss_tree = sum(rows[p][1] for p in descendants if p in rows)
        peak_tree = max(peak_tree, rss_tree * 1024)
        for pid in descendants:
            if pid in rows and Path(rows[pid][2]).name == 'lean':
                peak_lean = max(peak_lean, rows[pid][1] * 1024)
                if rows[pid][1] * 1024 > 8 * 1024 ** 3:
                    cap_killed = True
        if time.monotonic() - t0 > wall_cap_seconds:
            wall_killed = True
        if cap_killed or wall_killed or parallel_killed:
            os.killpg(proc.pid, signal.SIGKILL)
        time.sleep(0.10)
    rc = proc.wait()
b = log.read_bytes()
s = b.decode(errors='replace')
rss_time = re.findall(r'(\d+)\s+maximum resident set size', s)
record = dict(max_global_lean_count=peak_global_lean_count, parallel_lean_cap_killed=parallel_killed, mode=mode, command=cmd, time_wrapper=['/usr/bin/time', '-l'], cwd=str(Path.cwd()), exit_code=rc, elapsed_seconds=time.monotonic()-t0, sampled_single_lean_peak_bytes=peak_lean, sampled_tree_peak_bytes=peak_tree, time_maxrss_bytes=int(rss_time[-1]) if rss_time else None, rss_cap_bytes=8*1024**3, rss_cap_killed=cap_killed, wall_cap_seconds=wall_cap_seconds, wall_cap_killed=wall_killed, source=str(src), source_sha256_before=source_hash, source_sha256_after=hashlib.sha256(src.read_bytes()).hexdigest(), source_snapshot=str(snapshot), log=str(log), log_sha256=hashlib.sha256(b).hexdigest())
state.append(record)
(out / 'runs.json').write_text(json.dumps(state, indent=2)+'\n')
print(json.dumps(record))
for line in s.splitlines():
    if str(src) in line and ('error:' in line or 'warning:' in line or 'depends on axioms' in line):
        print(line)
if rc: print(s[-4500:])
sys.exit(rc)
