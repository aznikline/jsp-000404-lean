#!/usr/bin/env python3
"""Supplement a missing structured interval check without touching old evidence.

Run only after the root has allocated the one compiler slot. Existing PASS
sources, logs, receipts and normal build artifacts are never overwritten.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

from check_six_symbolic_kernel_20261005 import rss_tree, STANDARD

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'Jsp000404/SixExactFloorKernelSymbolicInterval.lean'
MODULE = 'Jsp000404.SixExactFloorKernelSymbolicInterval'
THEOREM = 'Jsp404.SixExactFloorKernel.score_gap_min_interval'
RECEIPT = 'research/JSP404_SIX_SYMBOLIC_BETWEEN_FRESH_RECHECK_20261006b.json'
LOGDIR = 'verification/six-symbolic-between-fresh-recheck-20261006b'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    frozen = json.loads((ROOT / 'research/JSP404_SIX_SYMBOLIC_BETWEEN_ALL62_FINAL_FREEZE_20261006.json').read_text())
    source = ROOT / SOURCE
    source_sha = sha(source)
    assert source_sha == frozen['proof_source_hashes'][SOURCE]
    directory = ROOT / LOGDIR
    directory.mkdir(exist_ok=True)
    receipt_path = ROOT / RECEIPT
    log = directory / 'interval-strict.txt'
    artifact = directory / 'SixExactFloorKernelSymbolicInterval.olean'
    if receipt_path.exists():
        prior = json.loads(receipt_path.read_text())
        if prior.get('status') == 'PASS':
            row = prior['results'][0]
            assert row['source_sha256'] == source_sha
            assert sha(ROOT / row['log']) == row['log_sha256']
            assert artifact.is_file() and sha(artifact) == row['artifact_sha256']
            print('Existing independent PASS receipt retained.', flush=True)
            return
        raise RuntimeError('Previous non-PASS evidence retained; use a new attempt name.')
    command = ['lake', 'env', 'lean', '--trust=0', '-DautoImplicit=false',
               '-o', str(artifact), str(source)]
    start, peak, stop = time.monotonic(), 0, None
    with log.open('w') as output:
        process = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        while process.poll() is None:
            rss, rows, owned = rss_tree(process.pid)
            peak = max(peak, rss)
            if rss >= 8 * 1024 ** 2 or time.monotonic() - start > 120:
                stop = 'RSS_CAP' if rss >= 8 * 1024 ** 2 else 'TIME_CAP'
                for pid, parent, memory in rows:
                    if pid in owned and not any(pp == pid for cc, pp, rr in rows):
                        subprocess.run(['kill', '-INT', str(pid)], check=False)
                break
            time.sleep(.1)
        try:
            process.wait(timeout=20)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
            stop = stop or 'TIME_CAP'
    text = log.read_text()
    axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
    success = (process.returncode == 0 and stop is None and 'error:' not in text
               and THEOREM in axioms and all(set(value.replace(',', ' ').split()) <= STANDARD
                                            for value in axioms.values())
               and artifact.is_file() and sha(source) == source_sha)
    row = {'stage': 'strict', 'module': MODULE, 'source': SOURCE, 'source_sha256': source_sha,
           'command': command, 'status': 'PASS' if success else 'NOT_PROVED',
           'exit_code': process.returncode, 'resource_stop': stop, 'rss_cap_gib': 8,
           'seconds': time.monotonic() - start, 'peak_tree_rss_kib': peak,
           'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
           'all_replayed_axioms': axioms, 'public_axioms': axioms.get(THEOREM),
           'artifact': str(artifact.relative_to(ROOT)),
           'artifact_sha256': sha(artifact) if artifact.is_file() else None}
    receipt = {'status': row['status'], 'concurrency': 1, 'expected_targets': 1,
               'completed': 1 if success else 0, 'scope': 'Independent trust=0 interval recheck; all-62 normal evidence is reused unchanged.',
               'source_freeze': 'research/JSP404_SIX_SYMBOLIC_BETWEEN_ALL62_FINAL_FREEZE_20261006.json',
               'source_freeze_sha256': sha(ROOT / 'research/JSP404_SIX_SYMBOLIC_BETWEEN_ALL62_FINAL_FREEZE_20261006.json'),
               'script': str(Path(__file__).resolve().relative_to(ROOT)),
               'script_sha256': sha(Path(__file__)), 'results': [row],
               'publish_files': [str(Path(__file__).resolve().relative_to(ROOT)), RECEIPT, str(log.relative_to(ROOT))],
               'local_artifact_only': str(artifact.relative_to(ROOT))}
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: row[key] for key in ['status', 'seconds', 'peak_tree_rss_kib', 'public_axioms']}), flush=True)
    if not success:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
