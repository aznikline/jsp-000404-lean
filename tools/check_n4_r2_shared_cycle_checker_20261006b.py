#!/usr/bin/env python3
"""Single-slot strict/normal checks; preserve every failed attempt log.

This checks only the shared checker module. It does not certify the external
24698-word catalog or the original eight-point theorem.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import signal
import subprocess
import time

from check_six_symbolic_kernel_20261005 import rss_tree, STANDARD

ROOT = Path(__file__).resolve().parents[1]
MODULE = 'Jsp000404.N4R2SharedCycleChecker'
SOURCE = 'Jsp000404/N4R2SharedCycleChecker.lean'
RECEIPT = 'research/JSP404_N4_R2_SHARED_CYCLE_CHECKER_RECEIPT_20261006b.json'
LOGDIR = 'verification/n4-r2-shared-cycle-checker-20261006b'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = ROOT / SOURCE
    source_sha = sha(source)
    receipt_path = ROOT / RECEIPT
    receipt = json.loads(receipt_path.read_text()) if receipt_path.exists() else {
        'status': 'RUNNING', 'concurrency': 1, 'rss_cap_gib': 8, 'attempts': [],
        'scope': 'Shared Boolean cycle checker and genuine actual-row bridges only; not kernel all24698/bare8.'}
    logs = ROOT / LOGDIR
    logs.mkdir(exist_ok=True)
    artifact = ROOT / '.lake/build/lib/lean/Jsp000404/N4R2SharedCycleChecker.olean'
    selected = ['Jsp404.N4R2SharedCycleChecker.' + name for name in
                re.findall(r'^#print axioms\s+(\S+)', source.read_text(), re.M)]
    current = []
    for stage in ('strict', 'normal'):
        number = 1 + sum(row['stage'] == stage for row in receipt['attempts'])
        log = logs / f'{stage}-attempt{number:02d}.txt'
        command = (['lake', 'env', 'lean', '--trust=0', '-M8192', '-DautoImplicit=false',
                    '-o', str(artifact), str(source)] if stage == 'strict' else ['lake', 'build', MODULE])
        start, peak, stop = time.monotonic(), 0, None
        with log.open('w') as output:
            process = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            while process.poll() is None:
                rss, _, _ = rss_tree(process.pid)
                peak = max(peak, rss)
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
        text = log.read_text()
        axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
        own_built = bool(re.search(r'\bBuilt ' + re.escape(MODULE) + r'(?:\s|$)', text))
        success = (process.returncode == 0 and stop is None and 'error:' not in text
                   and set(selected) <= set(axioms)
                   and all(set(value.replace(',', ' ').split()) <= STANDARD for value in axioms.values())
                   and artifact.is_file() and sha(source) == source_sha
                   and (stage == 'strict' or (own_built and 'Build completed successfully' in text)))
        row = {'stage': stage, 'attempt': number, 'module': MODULE, 'source': SOURCE,
               'source_sha256': source_sha, 'command': command, 'status': 'PASS' if success else 'NOT_PROVED',
               'exit_code': process.returncode, 'resource_stop': stop, 'rss_cap_gib': 8,
               'seconds': time.monotonic() - start, 'peak_tree_rss_kib': peak,
               'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
               'all_replayed_axioms': axioms, 'selected_axioms': {name: axioms.get(name) for name in selected},
               'own_target_built': own_built if stage == 'normal' else None,
               'artifact_sha256': sha(artifact) if artifact.is_file() else None}
        current.append(row)
        receipt['attempts'].append(row)
        receipt.update({'status': 'RUNNING' if success else 'NOT_PROVED', 'source_sha256': source_sha,
                        'script': str(Path(__file__).resolve().relative_to(ROOT)),
                        'script_sha256': sha(Path(__file__)), 'results': current,
                        'public_selected_declarations': selected, 'kernel_all_words': False,
                        'original_eight_point_complete': False})
        receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({key: row[key] for key in ['stage', 'attempt', 'status', 'seconds', 'peak_tree_rss_kib']}), flush=True)
        if not success:
            raise SystemExit(1)
    receipt['status'] = 'PASS'
    receipt['publish_files'] = [SOURCE, str(Path(__file__).resolve().relative_to(ROOT)), RECEIPT] + [
        row['log'] for row in receipt['attempts']]
    receipt['file_hashes'] = {path: sha(ROOT / path) for path in receipt['publish_files'] if path != RECEIPT}
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
