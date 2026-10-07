#!/usr/bin/env python3
"""Check exactly one new replay module, with immutable successful checkpoints.

Strict and genuine normal checks are sequential. Data-only modules are marked
as typed data, not arithmetic acceptance proofs. Every failed source/stdout is
archived exactly; no root/full build is run.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

from check_six_symbolic_kernel_20261005 import rss_tree, STANDARD

ROOT = Path(__file__).resolve().parents[1]
CHECKPOINT = 'research/JSP404_N4_R2_SHARED_REPLAY_CHECKPOINT_20261007.json'
LOGDIR = 'verification/n4-r2-shared-replay-20261007'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('module')
    parser.add_argument('--rss-gib', type=float, default=8)
    parser.add_argument('--seconds', type=float, default=300)
    args = parser.parse_args()
    assert re.fullmatch(r'Jsp000404\.N4R2[A-Za-z0-9]+', args.module)
    assert 0 < args.rss_gib <= 8 and 0 < args.seconds <= 600
    relative = args.module.replace('.', '/') + '.lean'
    source = ROOT / relative
    before_bytes = source.read_bytes()
    source_sha = hashlib.sha256(before_bytes).hexdigest()
    text = before_bytes.decode()
    for token in ['sorry', 'admit', 'native_decide', 'axiom', 'newaxiom']:
        assert not re.search(r'\b' + token + r'\b', text), f'Forbidden token in new replay source: {token}'
    for imported in re.findall(r'^import\s+(Jsp000404\.[A-Za-z0-9_.]+)', text, re.M):
        imported_artifact = ROOT / '.lake/build/lib/lean' / Path(imported.replace('.', '/')).with_suffix('.olean')
        if not imported_artifact.is_file():
            raise RuntimeError(f'Check prerequisite separately first: {imported}')
    namespace = re.search(r'^namespace\s+(\S+)', text, re.M).group(1)
    names = re.findall(r'^#print axioms\s+(\S+)', text, re.M)
    selected = [name if name.startswith('Jsp404.') else namespace + '.' + name for name in names]
    checkpoint_path = ROOT / CHECKPOINT
    checkpoint = json.loads(checkpoint_path.read_text()) if checkpoint_path.exists() else {
        'status': 'PARTIAL', 'scope': 'Only explicitly checked new module targets; no full all-word claim.',
        'kernel_all_words': False, 'original_eight_point_complete': False,
        'modules': {}, 'passed_source_hashes': {}}
    artifact = ROOT / '.lake/build/lib/lean' / Path(relative).with_suffix('.olean')
    prior = checkpoint['modules'].get(args.module)
    if prior and prior.get('status') == 'PASS':
        assert prior['source_sha256'] == source_sha, 'Refusing to replace a completed source checkpoint'
        normal = prior['results'][-1]
        assert artifact.is_file() and sha(artifact) == normal['artifact_sha256']
        for row in prior['results']:
            assert sha(ROOT / row['log']) == row['log_sha256']
        print(json.dumps({'module': args.module, 'status': 'REUSED_EXACT_PASS'}), flush=True)
        return
    record = prior or {'status': 'RUNNING', 'attempts': []}
    record.update({'module': args.module, 'source': relative, 'source_sha256': source_sha,
                   'selected_declarations': selected,
                   'claim': 'closed printed proof declarations' if selected else 'typed finite definitions only'})
    checkpoint['modules'][args.module] = record
    module_logs = ROOT / LOGDIR / args.module.rsplit('.', 1)[1]
    module_logs.mkdir(parents=True, exist_ok=True)
    results = []
    for stage in ('strict', 'normal'):
        attempt = 1 + sum(row['stage'] == stage for row in record['attempts'])
        log = module_logs / f'{stage}-attempt{attempt:02d}.txt'
        command = (['lake', 'env', 'lean', '--trust=0', '-M8192', '-DautoImplicit=false',
                    '-o', str(artifact), str(source)] if stage == 'strict' else ['lake', 'build', args.module])
        start, peak, stop = time.monotonic(), 0, None
        with log.open('w') as output:
            process = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            while process.poll() is None:
                rss, _, _ = rss_tree(process.pid)
                peak = max(peak, rss)
                if rss >= args.rss_gib * 1024 ** 2 or time.monotonic() - start > args.seconds:
                    stop = 'RSS_CAP' if rss >= args.rss_gib * 1024 ** 2 else 'TIME_CAP'
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
        axioms.update({name: '' for name in re.findall(r"'([^']+)' does not depend on any axioms", output)})
        own_built = bool(re.search(r'\bBuilt ' + re.escape(args.module) + r'(?:\s|$)', output))
        success = (process.returncode == 0 and stop is None and sha(source) == source_sha
                   and artifact.is_file() and set(selected) <= set(axioms)
                   and all(set(value.replace(',', ' ').split()) <= STANDARD for value in axioms.values())
                   and (stage == 'strict' or (own_built and 'Build completed successfully' in output)))
        row = {'stage': stage, 'attempt': attempt, 'status': 'PASS' if success else 'NOT_PROVED',
               'source_sha256': source_sha, 'command': command, 'exit_code': process.returncode,
               'resource_stop': stop, 'rss_cap_gib': args.rss_gib, 'seconds': time.monotonic() - start,
               'peak_tree_rss_kib': peak, 'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
               'own_target_built': own_built if stage == 'normal' else None,
               'all_replayed_axioms': axioms, 'selected_axioms': {name: axioms.get(name) for name in selected},
               'artifact_sha256': sha(artifact) if artifact.is_file() else None}
        if not success:
            snapshot = module_logs / f'{stage}-attempt{attempt:02d}-failed-source.lean'
            snapshot.write_bytes(before_bytes)
            row['failed_source_snapshot'] = str(snapshot.relative_to(ROOT))
            row['failed_source_snapshot_sha256'] = sha(snapshot)
        results.append(row)
        record['attempts'].append(row)
        record.update({'status': 'RUNNING' if success else 'NOT_PROVED', 'results': results,
                       'script': str(Path(__file__).resolve().relative_to(ROOT)),
                       'script_sha256': sha(Path(__file__))})
        checkpoint_path.write_text(json.dumps(checkpoint, indent=2) + '\n')
        print(json.dumps({'module': args.module, **{key: row[key] for key in
                         ['stage', 'attempt', 'status', 'seconds', 'peak_tree_rss_kib']}}), flush=True)
        if not success:
            raise SystemExit(1)
    record['status'] = 'PASS'
    checkpoint['passed_source_hashes'][relative] = source_sha
    record['publish_files'] = [relative] + [row['log'] for row in record['attempts']]
    record['publish_files'] += [row['failed_source_snapshot'] for row in record['attempts'] if 'failed_source_snapshot' in row]
    checkpoint_path.write_text(json.dumps(checkpoint, indent=2) + '\n')


if __name__ == '__main__':
    main()
