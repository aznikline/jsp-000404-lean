#!/usr/bin/env python3
"""Run genuinely checked cases sequentially, pausing at complete case boundaries.

The optional stdin barrier is controlled by the producing agent for sharing the
single compiler window.  No stage status is inferred from solver diagnostics.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--masks', type=int, nargs='+', required=True)
    parser.add_argument('--gate-each-case', action='store_true')
    args = parser.parse_args()
    assert len(args.masks) <= 5 and len(set(args.masks)) == len(args.masks)
    for index, mask in enumerate(args.masks):
        freeze_path = ROOT / f'research/JSP404_SIX_SYMBOLIC_MASK{mask}_SOURCE_FREEZE_20261006.json'
        freeze = json.loads(freeze_path.read_text())
        for source, digest in freeze['source_hashes'].items():
            assert sha(ROOT / source) == digest, f'Frozen source changed: {source}'
        if freeze.get('kernel') != 'PASS' or freeze.get('normal_lake') != 'PASS':
            for stage in ('nat', 'actual', 'reflection', 'normal'):
                path = ROOT / f'research/JSP404_SIX_SYMBOLIC_M{mask}_{stage.upper()}_RECEIPT_20261006.json'
                print(json.dumps({'mask': mask, 'stage': stage, 'action': 'REAL_CHECK_OR_VALID_ARTIFACT_REUSE'}), flush=True)
                subprocess.run([sys.executable, str(ROOT / 'tools/check_six_symbolic_mask_kernel_20261006.py'),
                                '--mask', str(mask), '--stage', stage], cwd=ROOT, check=True)
                assert json.loads(path.read_text())['status'] == 'PASS'
            subprocess.run([sys.executable, str(ROOT / 'tools/freeze_six_symbolic_mask_20261006.py'),
                            '--mask', str(mask)], cwd=ROOT, check=True)
        freeze = json.loads(freeze_path.read_text())
        assert freeze['kernel'] == 'PASS' and freeze['normal_lake'] == 'PASS'
        print(json.dumps({'case_ready': mask, 'mirror': freeze['reflection_mask'],
                          'freeze': str(freeze_path.relative_to(ROOT)),
                          'remaining_in_this_cohort': args.masks[index + 1:]}), flush=True)
        if args.gate_each_case and index + 1 < len(args.masks):
            print('CASE_BOUNDARY_NO_LEAN_RUNNING: send next to continue or stop to exit.', flush=True)
            command = sys.stdin.readline().strip()
            if command != 'next':
                print(json.dumps({'status': 'STOPPED_AT_PROVED_CASE_BOUNDARY',
                                  'remaining': args.masks[index + 1:]}), flush=True)
                return
    print(json.dumps({'status': 'ALL_REQUESTED_CASES_READY', 'masks': args.masks}), flush=True)


if __name__ == '__main__':
    main()
