#!/usr/bin/env python3
"""One explicitly leased target, serial trust-zero and genuine normal checks.

Preparation never invokes a compiler. Every attempt retains exact source and
raw outputs. This tool does not dispatch later targets or publish to Git.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import runpy
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path(__file__).parent
MODULES = ['Jsp000404.ActualF18ThreeHeavyNoHO',
           'Jsp000404.ActualF18ThreeHeavy', 'Jsp000404.ActualF18Complete']
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def active_compilers():
    raw = subprocess.check_output(['ps', '-A', '-o', 'pid=,ppid=,rss=,comm='], text=True)
    return [line.strip() for line in raw.splitlines()
            if line.strip().split()[-1].rsplit('/', 1)[-1] in ('lean', 'lake')]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--module', choices=MODULES)
    parser.add_argument('--expected-sha')
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    if args.prepare_only:
        freeze = json.loads((DIRECTORY / 'precheck-source-freeze.json').read_text())
        for row in freeze['modules']:
            assert sha(ROOT / row['source']) == row['source_sha256']
            assert sha(ROOT / row['candidate_snapshot']) == row['source_sha256']
        print(json.dumps({'status': 'STATIC_QUEUE_READY_NO_COMPILER_RUN',
                          'modules': freeze['validation_order'], 'concurrency': 1}))
        return 0
    assert args.module and args.expected_sha and re.fullmatch('[0-9a-f]{64}', args.expected_sha)
    source = ROOT / (args.module.replace('.', '/') + '.lean')
    original = source.read_bytes()
    assert sha(source) == args.expected_sha
    text = original.decode()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom|newaxiom)\b', text)
    namespace = re.search(r'^namespace\s+(\S+)', text, re.M)[1]
    selected = [n if n.startswith('Jsp404.') else namespace + '.' + n
                for n in re.findall(r'^#print axioms\s+(\S+)', text, re.M)]
    assert len(selected) == 1
    for imported in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)', text, re.M):
        path = ROOT / '.lake/build/lib/lean' / (imported.replace('.', '/') + '.olean')
        assert path.exists(), ('Compile prerequisite separately first', imported)
    logs = DIRECTORY / args.module.rsplit('.', 1)[1]
    logs.mkdir(exist_ok=True)
    attempt = 1
    while (logs / f'run-attempt{attempt:02d}.json').exists():
        attempt += 1
    assert attempt <= 3, 'Root allowed at most three quick API attempts'
    output = logs / f'run-attempt{attempt:02d}.json'
    record = {'status': 'RUNNING', 'module': args.module,
              'source': str(source.relative_to(ROOT)), 'source_sha256': args.expected_sha,
              'selected_declarations': selected, 'runner': str(Path(__file__).relative_to(ROOT)),
              'runner_sha256': sha(__file__), 'rss_cap_gib': 8,
              'time_cap_seconds': 180, 'concurrency': 1, 'results': []}
    artifact = ROOT / '.lake/build/lib/lean' / (args.module.replace('.', '/') + '.olean')
    rss_tree = runpy.run_path(str(ROOT / 'tools/check_six_symbolic_kernel_20261005.py'))['rss_tree']
    for stage in ['strict', 'normal']:
        assert not active_compilers(), 'Another Lean/Lake process is active'
        assert sha(source) == args.expected_sha
        index = 1
        while (logs / f'{stage}-attempt{index:02d}.txt').exists():
            index += 1
        log = logs / f'{stage}-attempt{index:02d}.txt'
        snapshot = logs / f'{stage}-attempt{index:02d}.source.lean'
        snapshot.write_bytes(original)
        command = (['lake', 'env', 'lean', '--trust=0', '-DautoImplicit=false', '-M8192',
                    '-o', str(artifact), str(source)] if stage == 'strict' else
                   ['lake', 'build', args.module])
        start, peak, stop = time.monotonic(), 0, None
        with log.open('wb') as raw:
            process = subprocess.Popen(command, cwd=ROOT, stdout=raw,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            while process.poll() is None:
                rss, _, _ = rss_tree(process.pid)
                peak = max(peak, rss)
                if rss >= 8 * 1024**2 or time.monotonic() - start > 180:
                    stop = 'RSS_CAP' if rss >= 8 * 1024**2 else 'TIME_CAP'
                    os.killpg(process.pid, signal.SIGINT)
                    break
                time.sleep(.1)
            try:
                process.wait(timeout=20)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                stop = stop or 'EXIT_TIMEOUT'
        raw = log.read_text()
        groups = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", raw, re.S)
        groups += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", raw)]
        observed = {n: [a for k, a in groups if k == n] for n in selected}
        axes = {n: rows[0] if len(rows) == 1 else None for n, rows in observed.items()}
        built = bool(re.search(r'\bBuilt\s+' + re.escape(args.module) + r'(?:\s|$)', raw))
        success = (process.returncode == 0 and stop is None and sha(source) == args.expected_sha
                   and artifact.exists() and not re.search(r'(^|\n).*\berror:', raw)
                   and all(a is not None and set(a.replace(',', ' ').split()) <= STANDARD
                           for a in axes.values())
                   and (stage != 'normal' or built and 'Build completed successfully' in raw))
        warnings = [line for line in raw.splitlines()
                    if str(source.relative_to(ROOT)) + ':' in line and 'warning:' in line]
        row = {'stage': stage, 'attempt': index, 'status': 'PASS' if success else 'NOT_PROVED',
               'command': command, 'source_sha256': args.expected_sha,
               'exit_code': process.returncode, 'resource_stop': stop,
               'seconds': time.monotonic() - start, 'peak_tree_rss_kib': peak,
               'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
               'source_snapshot': str(snapshot.relative_to(ROOT)), 'source_snapshot_sha256': sha(snapshot),
               'selected_axioms': axes, 'own_target_built': built if stage == 'normal' else None,
               'artifact_sha256': sha(artifact) if artifact.exists() else None, 'own_warnings': warnings}
        record['results'].append(row)
        record['status'] = 'RUNNING' if success else 'NOT_PROVED'
        output.write_text(json.dumps(record, indent=2) + '\n')
        print(json.dumps({k: row[k] for k in ['stage', 'attempt', 'status', 'exit_code',
              'resource_stop', 'seconds', 'peak_tree_rss_kib', 'selected_axioms',
              'own_target_built', 'own_warnings']}), flush=True)
        if not success:
            print('\n'.join(line for line in raw.splitlines() if 'error:' in line)[-5000:], flush=True)
            return 1
    record['status'] = 'PASS_EXACT_SOURCE_STRICT_AND_GENUINE_NORMAL'
    record['all_dispatched_processes_exited'] = not active_compilers()
    output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': record['status'], 'module': args.module,
                      'receipt': str(output.relative_to(ROOT)), 'sha256': sha(output)}), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
