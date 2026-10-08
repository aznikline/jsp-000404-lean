#!/usr/bin/env python3
"""Check only the owned owned five remainder-group03-16 group candidates, with one 8 GiB Lean process tree."""
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

MANIFEST_PATH = Path(__file__).resolve().parent / 'compile-plan.json'
MANIFEST = json.loads(MANIFEST_PATH.read_text())
MODULE = sys.argv[1]
assert MODULE in MANIFEST['modules'], 'Only the five remainder-group03-16 group candidates are allowed'
ITEM = MANIFEST['modules'][MODULE]
SOURCE = ROOT / ITEM['source']
LOGDIR = Path(__file__).resolve().parent / MODULE.split('.')[-1]
LOGDIR.mkdir(exist_ok=True)
CHECKPOINT = LOGDIR / 'checkpoint.json'
ARTIFACT = ROOT / '.lake/build/lib/lean' / Path(*MODULE.split('.')).with_suffix('.olean')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    stage = sys.argv[2]
    assert stage in ('strict', 'normal')
    before = SOURCE.read_bytes()
    source_sha = sha(SOURCE)
    text = before.decode()
    selected = ITEM['selected']
    assert source_sha == ITEM['approved_source_sha256'], 'Candidate hash changed without repair record'
    assert all(sha(ROOT / path) == h for path, h in MANIFEST['protected_existing_sources'].items()), 'Protected PASS source changed'
    current_namespace, actual_prints = None, []
    for line in text.splitlines():
        namespace = re.match(r'^namespace\s+(\S+)', line)
        if namespace:
            current_namespace = namespace.group(1)
        declaration = re.match(r'^#print axioms\s+(\S+)', line)
        if declaration:
            short = declaration.group(1)
            actual_prints.append(short if short.startswith('Jsp404.') else current_namespace + '.' + short)
        if line.startswith('end Jsp404.'):
            current_namespace = None
    assert selected == actual_prints
    for dep in ITEM['imports']:
        if dep in MANIFEST['modules']:
            prior_path = Path(__file__).resolve().parent / dep.split('.')[-1] / 'checkpoint.json'
            assert prior_path.is_file(), 'Owned dependency not checked yet: ' + dep
            prior_record = json.loads(prior_path.read_text())
            normals = [r for r in prior_record['attempts'] if r['stage'] == 'normal']
            assert normals and normals[-1]['status'] == 'PASS'
            assert normals[-1]['source_sha256'] == sha(ROOT / MANIFEST['modules'][dep]['source'])
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
            process_rows = subprocess.check_output(['ps', '-A', '-o', 'pid=,comm='], text=True)
            lean_count = sum(bool(line.split()) and Path(line.split(maxsplit=1)[1]).name == 'lean' for line in process_rows.splitlines())
            if lean_count > 1:
                stop = 'MULTIPLE_LEAN'
                os.killpg(process.pid, signal.SIGINT)
                break
            if rss >= 8 * 1024 ** 2 or time.monotonic() - start > 180:
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
          all(sha(ROOT / path) == h for path, h in MANIFEST['protected_existing_sources'].items()) and
          (stage == 'strict' or (own_built and 'Build completed successfully' in output)))
    row = {'stage': stage, 'attempt': attempt, 'status': 'PASS' if ok else 'NOT_PROVED',
           'source_sha256': source_sha, 'selected_count': len(selected), 'definitions_only_no_prints': not selected, 'command': command, 'exit_code': process.returncode,
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
