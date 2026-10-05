#!/usr/bin/env python3
"""Prepare a small new cohort without rewriting any frozen PASS case."""
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
    args = parser.parse_args()
    assert len(args.masks) <= 5 and len(set(args.masks)) == len(args.masks)
    schedule = json.loads((ROOT / 'research/JSP404_SIX_SYMBOLIC_REMAINING_SCHEDULE_20261006.json').read_text())
    remaining = {c['mask']: c for c in schedule['results']}
    results = []
    for mask in args.masks:
        assert mask in remaining
        freeze = ROOT / f'research/JSP404_SIX_SYMBOLIC_MASK{mask}_SOURCE_FREEZE_20261006.json'
        assert not freeze.exists(), f'Case {mask} already has a freeze; preserve it.'
        assert not list((ROOT / 'Jsp000404').glob(f'SixExactFloorKernelSymbolicMask{mask:03d}*.lean'))
        for script, flag in (
            ('export_six_symbolic_mask_kernel_20261006.py', '--mask'),
            ('export_six_symbolic_cohort_reflection_20261006.py', '--proved-mask'),
        ):
            subprocess.run([sys.executable, str(ROOT / 'tools' / script), flag, str(mask)],
                           cwd=ROOT, check=True)
        sources = sorted((ROOT / 'Jsp000404').glob(f'SixExactFloorKernelSymbolicMask{mask:03d}*.lean'))
        manifest = json.loads((ROOT / f'research/JSP404_SIX_SYMBOLIC_M{mask}_NAT_SHARDS_MANIFEST_20261006.json').read_text())
        assert len(sources) == remaining[mask]['nat_shards'] + 3
        assert manifest['total_leaves'] == remaining[mask]['pruned_leaves']
        assert max(s['leaves'] for s in manifest['shards']) <= 300
        data = {
            'mask': mask, 'source_hashes': {str(p.relative_to(ROOT)): sha(p) for p in sources},
            'nat_shards': len(manifest['shards']), 'nat_leaves': manifest['total_leaves'],
            'kernel': 'NOT_RUN', 'normal_lake': 'NOT_RUN',
            'scope': 'Fixed direction and typed reflection, ModelSix n, n>=4 HIGH, defects(2,3,*,3,2)',
            'mathematical_fingerprint_sha256': remaining[mask]['fingerprint_sha256'],
            'preparer': str(Path(__file__).resolve().relative_to(ROOT)),
            'preparer_sha256': sha(Path(__file__).resolve()),
        }
        freeze.write_text(json.dumps(data, indent=2) + '\n')
        results.append({'mask': mask, 'sources': len(sources),
                        'nat_leaves': data['nat_leaves'],
                        'bytes': sum(p.stat().st_size for p in sources),
                        'freeze': str(freeze.relative_to(ROOT))})
    print(json.dumps({'status': 'SOURCE_ONLY_NOT_PROVED', 'cases': results,
                      'total_sources': sum(x['sources'] for x in results),
                      'total_bytes': sum(x['bytes'] for x in results)}), flush=True)


if __name__ == '__main__':
    main()
