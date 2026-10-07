#!/usr/bin/env python3
"""Bounded batches of thin targets; at most two process trees totaling 6 GiB.

Only run in a root-allocated thin-data window. Never alongside actual geometry
or a full audit. Each child has its own durable ledger; aggregation uses a lock.
"""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import argparse
import fcntl
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MASTER = ROOT / 'research/JSP404_N4_R2_SHARED_REPLAY_CHECKPOINT_20261007.json'
MANIFEST = ROOT / 'research/JSP404_N4_R2_SHARED_REPLAY_SOURCE_MANIFEST_20261007.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def merge(module):
    path = ROOT / f'research/n4-r2-replay-module-checkpoints-20261007/{module.rsplit(".", 1)[1]}.json'
    if not path.is_file():
        return
    ledger = json.loads(path.read_text())
    record = ledger['modules'][module]
    if record['status'] == 'PASS':
        assert sha(ROOT / record['source']) == record['source_sha256']
        for row in record['results']:
            assert sha(ROOT / row['log']) == row['log_sha256']
        artifact = ROOT / '.lake/build/lib/lean' / Path(record['source']).with_suffix('.olean')
        assert sha(artifact) == record['results'][-1]['artifact_sha256']
    lock_path = ROOT / 'research/.n4-r2-replay-checkpoint.lock'
    with lock_path.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        master = json.loads(MASTER.read_text()) if MASTER.exists() else {
            'status': 'PARTIAL', 'kernel_all_words': False, 'original_eight_point_complete': False,
            'modules': {}, 'passed_source_hashes': {}}
        master['modules'][module] = record
        if record['status'] == 'PASS':
            master['passed_source_hashes'][record['source']] = record['source_sha256']
        master.setdefault('isolated_ledgers', {})[module] = {
            'path': str(path.relative_to(ROOT)), 'sha256': sha(path)}
        temporary = MASTER.with_suffix('.json.batch-tmp')
        temporary.write_text(json.dumps(master, indent=2) + '\n')
        temporary.replace(MASTER)
        fcntl.flock(lock, fcntl.LOCK_UN)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=['cycle-data', 'leaf-data', 'leaf-checks', 'tree', 'library', 'aggregate'], required=True)
    parser.add_argument('--workers', type=int, choices=[1, 2], default=1)
    parser.add_argument('--limit', type=int, default=1)
    parser.add_argument('--seconds', type=float, default=300)
    args = parser.parse_args()
    assert args.limit > 0 and 0 < args.seconds <= 600
    manifest = json.loads(MANIFEST.read_text())
    kind = {'cycle-data': 'finite_cycle_data', 'leaf-data': 'finite_leaf_data',
            'leaf-checks': 'closed_leaf_kernel_check', 'library': 'cycle_library',
            'aggregate': 'aggregate_leaf_kernel_checks'}.get(args.phase)
    modules = ([f'Jsp000404.N4R2WordTreeShard{i:03d}' for i in range(16)]
               if args.phase == 'tree' else [
                   module for module in manifest['kernel_check_order']
                   if manifest['module_kinds'][module] == kind])
    master = json.loads(MASTER.read_text()) if MASTER.exists() else {'modules': {}}
    todo = []
    for module in modules:
        old = master['modules'].get(module)
        if old and old['status'] == 'PASS':
            assert sha(ROOT / old['source']) == old['source_sha256']
            artifact = ROOT / '.lake/build/lib/lean' / Path(old['source']).with_suffix('.olean')
            assert sha(artifact) == old['results'][-1]['artifact_sha256']
            continue
        todo.append(module)
    todo = todo[:args.limit]
    cap = 3 if args.workers == 2 else 8
    stop_marker = ROOT / 'research/N4_R2_REPLAY_BATCH_STOP_AT_BOUNDARY'

    def run(module):
        command = [sys.executable, '-B', str(ROOT / 'tools/check_n4_r2_replay_isolated_20261007.py'),
                   module, '--rss-gib', str(cap), '--seconds', str(args.seconds)]
        process = subprocess.run(command, cwd=ROOT)
        merge(module)
        return module, process.returncode

    # Submit at most workers targets. On any failure, schedule no replacement;
    # let the already-active independently capped target finish and retain logs.
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        pending, position, failed = {}, 0, False
        while position < len(todo) and len(pending) < args.workers:
            future = pool.submit(run, todo[position])
            pending[future] = todo[position]
            position += 1
        while pending:
            done, _ = wait(pending, return_when=FIRST_COMPLETED)
            for future in done:
                pending.pop(future)
                module, code = future.result()
                failed = failed or code != 0
                print(json.dumps({'batch_module': module, 'exit_code': code}), flush=True)
            while not failed and not stop_marker.exists() and position < len(todo) and len(pending) < args.workers:
                future = pool.submit(run, todo[position])
                pending[future] = todo[position]
                position += 1
        if failed:
            raise SystemExit(1)
        if stop_marker.exists() and position < len(todo):
            print(json.dumps({'status': 'STOPPED_AT_MODULE_BOUNDARY',
                              'remaining_in_requested_batch': len(todo) - position}), flush=True)


if __name__ == '__main__':
    main()
