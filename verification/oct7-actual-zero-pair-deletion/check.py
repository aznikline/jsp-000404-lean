#!/usr/bin/env python3
"""Check only the owned zero-pair leaf, with one 8 GiB Lean process tree."""
from pathlib import Path
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from check_six_symbolic_kernel_20261005 import rss_tree, STANDARD

MODULE = 'Jsp000404.ActualZeroPairDeletionBudget'
SOURCE = ROOT / 'Jsp000404/ActualZeroPairDeletionBudget.lean'
LOGDIR = Path(__file__).resolve().parent
CHECKPOINT = LOGDIR / 'checkpoint.json'
ARTIFACT = ROOT / '.lake/build/lib/lean/Jsp000404/ActualZeroPairDeletionBudget.olean'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    stage = sys.argv[1]
    assert stage in ('strict', 'normal')
    before = SOURCE.read_bytes()
    source_sha = sha(SOURCE)
    text = before.decode()
    selected = ['Jsp404.ActualZeroPairDeletionBudget.' + name
                for name in re.findall(r'^#print axioms\s+(\S+)', text, re.M)]
    assert len(selected) == 4
    for token in ('sorry', 'admit', 'native_decide', 'axiom', 'newaxiom'):
        assert not re.search(r'\b' + token + r'\b', text), token
    rows = subprocess.check_output(['ps', '-A', '-o', 'pid=,comm='], text=True)
    active = [line for line in rows.splitlines()
              if line.split() and Path(line.split(maxsplit=1)[1]).name == 'lean']
    assert not active, 'Another Lean process is already active: ' + str(active)
    record = json.loads(CHECKPOINT.read_text()) if CHECKPOINT.exists() else {
        'module': MODULE, 'attempts': [], 'status': 'NOT_PROVED'}
    if stage == 'normal':
        prior = [r for r in record['attempts'] if r['stage'] == 'strict'][-1]
        assert prior['status'] == 'PASS' and prior['source_sha256'] == source_sha
    attempt = 1 + sum(r['stage'] == stage for r in record['attempts'])
    stem = f'{stage}-attempt{attempt:02d}'
    snapshot = LOGDIR / (stem + '.source.lean')
    log = LOGDIR / (stem + '.stdout.txt')
    assert not snapshot.exists() and not log.exists()
    snapshot.write_bytes(before)
    command = (['lake', 'env', 'lean', '--trust=0', '-M8192', '-DautoImplicit=false',
                '-o', str(ARTIFACT), str(SOURCE)] if stage == 'strict'
               else ['lake', 'build', MODULE])
    start, peak, stop = time.monotonic(), 0, None
    with log.open('w') as output:
        process = subprocess.Popen(command, cwd=ROOT, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        while process.poll() is None:
            rss, _, _ = rss_tree(process.pid)
            peak = max(peak, rss)
            if rss >= 8 * 1024 ** 2 or time.monotonic() - start > 300:
                stop = 'RSS_CAP' if rss >= 8 * 1024 ** 2 else 'TIME_CAP'
                os.killpg(process.pid, signal.SIGINT)
                break
            time.sleep(.1)
        try:
            process.wait(timeout=20)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            stop = stop or 'TIME_CAP'
    output = log.read_text()
    axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
    axioms.update({name: '' for name in re.findall(
        r"'([^']+)' does not depend on any axioms", output)})
    chosen = {name: axioms.get(name) for name in selected}
    std = all(chosen[name] is not None and
              set(chosen[name].replace(',', ' ').split()) <= STANDARD for name in selected)
    own_built = bool(re.search(r'\bBuilt ' + re.escape(MODULE) + r'(?:\s|$)', output))
    ok = (process.returncode == 0 and stop is None and sha(SOURCE) == source_sha and
          ARTIFACT.is_file() and std and
          (stage == 'strict' or (own_built and 'Build completed successfully' in output)))
    row = {'stage': stage, 'attempt': attempt, 'status': 'PASS' if ok else 'NOT_PROVED',
           'source_sha256': source_sha, 'command': command, 'exit_code': process.returncode,
           'resource_stop': stop, 'rss_cap_gib': 8, 'seconds': time.monotonic() - start,
           'peak_tree_rss_kib': peak, 'stdout': str(log.relative_to(ROOT)),
           'stdout_sha256': sha(log), 'source_snapshot': str(snapshot.relative_to(ROOT)),
           'source_snapshot_sha256': sha(snapshot), 'selected_axioms': chosen,
           'selected_standard_axioms_gate': std,
           'own_target_built': own_built if stage == 'normal' else None,
           'artifact_sha256': sha(ARTIFACT) if ARTIFACT.is_file() else None}
    record['attempts'].append(row)
    record['status'] = ('PASS' if ok and stage == 'normal' else
                        'STRICT_PASS_NORMAL_PENDING' if ok else 'NOT_PROVED')
    record['runner_sha256'] = sha(Path(__file__))
    CHECKPOINT.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(row, indent=2), flush=True)
    if not ok:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
