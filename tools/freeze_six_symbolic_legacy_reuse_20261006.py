#!/usr/bin/env python3
"""Freeze only the actually checked seven common-profile legacy adapters."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest_path = ROOT / 'research/JSP404_SIX_SYMBOLIC_LEGACY_REUSE_SOURCE_MANIFEST_20261006.json'
    receipt_path = ROOT / 'research/JSP404_SIX_SYMBOLIC_LEGACY_REUSE_CHECK_RECEIPT_20261006.json'
    manifest = json.loads(manifest_path.read_text())
    receipt = json.loads(receipt_path.read_text())
    assert receipt['status'] == 'PASS'
    assert {r['stage'] for r in receipt['results']} == {'strict', 'normal'}
    assert sha(ROOT / manifest['source']) == manifest['source_sha256']
    assert sha(ROOT / manifest['legacy_source']) == manifest['legacy_source_sha256']
    artifact = ROOT / '.lake/build/lib/lean/Jsp000404/SixSymbolicLegacyReuse.olean'
    for result in receipt['results']:
        assert result['status'] == 'PASS' and result['exit_code'] == 0
        assert result['resource_stop'] is None
        assert result['source_sha256'] == manifest['source_sha256']
        assert sha(ROOT / result['log']) == result['log_sha256']
        assert len(result['axioms']) == 7
        assert all(set(a.replace(',', ' ').split()) <=
                   {'propext', 'Classical.choice', 'Quot.sound'}
                   for a in result['axioms'].values())
    assert sha(artifact) == receipt['results'][-1]['artifact_sha256']
    freeze_path = ROOT / 'research/JSP404_SIX_SYMBOLIC_LEGACY_REUSE_FREEZE_20261006.json'
    whitelist = [
        manifest['source'],
        'tools/export_six_symbolic_legacy_reuse_20261006.py',
        'tools/check_six_symbolic_legacy_reuse_20261006.py',
        'tools/freeze_six_symbolic_legacy_reuse_20261006.py',
        str(manifest_path.relative_to(ROOT)),
        str(receipt_path.relative_to(ROOT)),
        str(freeze_path.relative_to(ROOT)),
    ] + [r['log'] for r in receipt['results']]
    if receipt.get('initial_receipt'):
        assert sha(ROOT / receipt['initial_receipt']) == receipt['initial_receipt_sha256']
        whitelist.append(receipt['initial_receipt'])
    freeze = {
        'status': 'READY_STRICT_AND_GENUINE_NORMAL_PASS',
        'source': manifest['source'], 'source_sha256': manifest['source_sha256'],
        'module': manifest['module'],
        'strict_and_normal_receipt': str(receipt_path.relative_to(ROOT)),
        'source_manifest': str(manifest_path.relative_to(ROOT)),
        'artifact_sha256': sha(artifact),
        'legacy_source': manifest['legacy_source'],
        'legacy_source_sha256': manifest['legacy_source_sha256'],
        'public_scope': manifest['scope'],
        'exact_common_profile_masks_added': manifest['exact_masks'],
        'declarations': manifest['declarations'],
        'standard_axioms': receipt['results'][0]['axioms'],
        'whitelist': whitelist,
        'file_hashes': {p: sha(ROOT / p) for p in whitelist
                       if p != str(freeze_path.relative_to(ROOT))},
        'full_all_62_exclusion_proved': False,
    }
    freeze_path.write_text(json.dumps(freeze, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'status': freeze['status'], 'freeze': str(freeze_path.relative_to(ROOT)),
                      'source_sha256': freeze['source_sha256'],
                      'masks': manifest['exact_masks'], 'whitelist_count': len(whitelist)}))


if __name__ == '__main__':
    main()
