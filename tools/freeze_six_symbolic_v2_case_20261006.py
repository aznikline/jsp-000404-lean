#!/usr/bin/env python3
"""Bind a V2 source family to actual strict and genuine Lake receipts."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mask', type=int, required=True)
    args = parser.parse_args()
    mask = args.mask
    path = ROOT / f'research/JSP404_SIX_SYMBOLIC_V2_MASK{mask}_SOURCE_FREEZE_20261006.json'
    f = json.loads(path.read_text())
    receipts = {}
    for stage in ('NAT', 'ACTUAL', 'REFLECTION', 'NORMAL'):
        p = ROOT / f'research/JSP404_SIX_SYMBOLIC_V2_M{mask}_{stage}_RECEIPT_20261006.json'
        r = json.loads(p.read_text())
        assert r['status'] == 'PASS'
        for result in r['results']:
            assert result['status'] == 'PASS' and result['exit_code'] == 0 and result['resource_stop'] is None
            assert sha(ROOT / result['source']) == result['source_sha256'] == f['source_hashes'][result['source']]
            assert sha(ROOT / result['log']) == result['log_sha256']
            assert all(set(ax.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
                       for ax in result['axioms'])
            if stage == 'NORMAL':
                assert sha(ROOT / '.lake/build/lib/lean' / Path(result['source']).with_suffix('.olean')) == result['artifact_sha256']
        receipts[stage] = {'path': str(p.relative_to(ROOT)), 'sha256': sha(p)}
    for source, digest in f['helper_source_hashes'].items():
        assert sha(ROOT / source) == digest
    manifest = ROOT / f'research/JSP404_SIX_SYMBOLIC_V2_M{mask}_NAT_SHARDS_MANIFEST_20261006.json'
    m = json.loads(manifest.read_text())
    assert m['fingerprint_sha256'] == f['fingerprint_sha256']
    canonical = json.dumps(m['fingerprint_payload'], sort_keys=True, separators=(',', ':')).encode()
    assert hashlib.sha256(canonical).hexdigest() == f['fingerprint_sha256']
    permutation = [9, 8, 5, 7, 4, 2, 6, 3, 1, 0]
    mirror = sum(((mask >> i) & 1) << j for i, j in enumerate(permutation))
    f.update({'kernel': 'PASS', 'normal_lake': 'PASS', 'reflection_mask': mirror,
              'covered_new_directions': [mask] if mirror == mask else [mask, mirror],
              'strict_sources': len(f['source_hashes']), 'normal_sources': len(f['source_hashes']),
              'public_imports': [f'Jsp000404.SixExactFloorKernelSymbolicV2Mask{mask:03d}Probe',
                                 f'Jsp000404.SixExactFloorKernelSymbolicV2Mask{mask:03d}Reflection'],
              'public_theorems': [f'Jsp404.SixExactFloorKernel.symbolic_v2_mask{mask}_probe',
                  f'Jsp404.SixExactFloorKernel.symbolic_v2_mask{mirror}_probe' if mirror != mask else
                  f'Jsp404.SixExactFloorKernel.symbolic_v2_mask{mirror}_reflection_transport'],
              'normal_seconds': sum(r['seconds'] for r in json.loads((ROOT / receipts['NORMAL']['path']).read_text())['results']),
              'normal_peak_tree_rss_kib': max(r['sampled_peak_tree_rss_kib'] for r in json.loads((ROOT / receipts['NORMAL']['path']).read_text())['results']),
              'receipts': receipts})
    generators = ['tools/export_six_symbolic_v2_kernel_20261006.py',
                  'tools/check_six_symbolic_v2_kernel_20261006.py',
                  'tools/freeze_six_symbolic_v2_case_20261006.py']
    f['publish_files'] = list(f['source_hashes']) + generators + [str(path.relative_to(ROOT)),
        str(manifest.relative_to(ROOT)), 'research/JSP404_SIX_SYMBOLIC_V2_BUDGET_HELPERS_FREEZE_20261006.json'] + \
        [r['path'] for r in receipts.values()] + \
        [f'verification/six-symbolic-v2-mask{mask}-{stage}-20261006' for stage in ('nat', 'actual', 'reflection', 'normal')]
    f['generator_hashes'] = {p: sha(ROOT / p) for p in generators}
    path.write_text(json.dumps(f, indent=2) + '\n')
    print(json.dumps({'mask': mask, 'mirror': mirror, 'status': 'STRICT_AND_TRUE_NORMAL_PASS',
                      'sources': len(f['source_hashes']), 'nat_leaves': f['nat_leaves'],
                      'normal_seconds': f['normal_seconds'], 'peak_gib': f['normal_peak_tree_rss_kib'] / 1024 ** 2,
                      'freeze': str(path.relative_to(ROOT))}))


if __name__ == '__main__':
    main()
