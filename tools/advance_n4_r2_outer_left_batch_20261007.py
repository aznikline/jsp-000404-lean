#!/usr/bin/env python3
"""Root-allocated outer-left batch, at most two3GiB process trees.

Every target gets genuine strict and normal checks. Any failure stops further
dispatch; a stop marker drains active targets at module boundaries.
"""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MASTER = ROOT / 'research/JSP404_N4_R2_OUTER_LEFT_CHECKPOINT_20261007.json'
MANIFEST = ROOT / 'research/JSP404_N4_R2_OUTER_LEFT_SOURCE_MANIFEST_20261007.json'
STOP = ROOT / 'research/N4_R2_OUTER_LEFT_STOP_AT_BOUNDARY'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def merge(module):
    path = ROOT / f'research/n4-r2-outer-left-module-checkpoints-20261007/{module.rsplit(".", 1)[1]}.json'
    if not path.exists():
        return
    record = json.loads(path.read_text())['modules'][module]
    if record['status'] == 'PASS':
        assert sha(ROOT / record['source']) == record['source_sha256']
        for result in record['results']:
            assert sha(ROOT / result['log']) == result['log_sha256']
        artifact = ROOT / '.lake/build/lib/lean' / Path(record['source']).with_suffix('.olean')
        assert sha(artifact) == record['results'][-1]['artifact_sha256']
    with (ROOT / 'research/.n4-r2-outer-left-checkpoint.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        data = json.loads(MASTER.read_text())
        data['modules'][module] = record
        if record['status'] == 'PASS':
            data['passed_source_hashes'][record['source']] = record['source_sha256']
        data.setdefault('isolated_ledgers', {})[module] = {'path': str(path.relative_to(ROOT)), 'sha256': sha(path)}
        temporary = MASTER.with_suffix('.json.batch-tmp')
        temporary.write_text(json.dumps(data, indent=2) + '\n')
        temporary.replace(MASTER)
        fcntl.flock(lock, fcntl.LOCK_UN)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, choices=[1, 2], default=2)
    parser.add_argument('--limit', type=int, default=193)
    parser.add_argument('--seconds', type=float, default=90)
    args = parser.parse_args()
    assert args.limit > 0 and 0 < args.seconds <= 180
    manifest, master = json.loads(MANIFEST.read_text()), json.loads(MASTER.read_text())
    todo = []
    for module, block in sorted(manifest['blocks'].items()):
        assert sha(ROOT / block['source']) == block['source_sha256']
        old = master['modules'].get(module)
        if old and old['status'] == 'PASS':
            assert old['source_sha256'] == block['source_sha256']
            artifact = ROOT / '.lake/build/lib/lean' / Path(old['source']).with_suffix('.olean')
            assert sha(artifact) == old['results'][-1]['artifact_sha256']
        else:
            todo.append(module)
    todo = todo[:args.limit]

    def run(module):
        command = [sys.executable, '-B', str(ROOT / 'tools/check_n4_r2_outer_left_isolated_20261007.py'),
                   module, '--rss-gib', '3', '--seconds', str(args.seconds)]
        process = subprocess.run(command, cwd=ROOT)
        merge(module)
        return module, process.returncode

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        pending, position, failed = {}, 0, False
        while position < len(todo) and len(pending) < args.workers and not STOP.exists():
            f = pool.submit(run, todo[position]); pending[f] = todo[position]; position += 1
        while pending:
            done, _ = wait(pending, return_when=FIRST_COMPLETED)
            for f in done:
                pending.pop(f)
                module, code = f.result()
                failed = failed or code != 0
                print(json.dumps({'batch_module': module, 'exit_code': code}), flush=True)
            while not failed and not STOP.exists() and position < len(todo) and len(pending) < args.workers:
                f = pool.submit(run, todo[position]); pending[f] = todo[position]; position += 1
        if failed:
            raise SystemExit(1)
        if STOP.exists() and position < len(todo):
            print(json.dumps({'status': 'STOPPED_AT_MODULE_BOUNDARY', 'remaining': len(todo) - position}), flush=True)


if __name__ == '__main__':
    main()
