#!/usr/bin/env python3
"""Freeze exact all-word producer evidence, refusing any missing kernel target.

This only packages existing genuine records. It never runs Lean or manufactures
success. The final actual Fin8 consumer and original lower theorem are separate.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECKPOINT = 'research/JSP404_N4_R2_SHARED_REPLAY_CHECKPOINT_20261007.json'
OUTPUT = 'research/JSP404_N4_R2_BETWEEN_REPLAY_FINAL_FREEZE_20261007.json'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
MODULES = (['Jsp000404.N4R2WordCatalog'] +
           [f'Jsp000404.N4R2WordTreeShard{i:03d}' for i in range(16)] +
           ['Jsp000404.N4R2WordCatalogComplete', 'Jsp000404.N4R2ModelCatalog'] +
           [f'Jsp000404.N4R2LeafCheckedShard{i:03d}' for i in range(193)] +
           ['Jsp000404.N4R2AllLeavesChecked', 'Jsp000404.N4R2BetweenTerminal'])


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ledger = json.loads((ROOT / CHECKPOINT).read_text())
    missing = [m for m in MODULES if ledger['modules'].get(m, {}).get('status') != 'PASS']
    if missing:
        raise SystemExit(f'NOT_READY: {len(missing)} required targets are not PASS; first={missing[0]}')
    records, selected, files, own_warnings = {}, {}, set(), []
    for module in MODULES:
        record = ledger['modules'][module]
        assert sha(ROOT / record['source']) == record['source_sha256']
        strict, normal = record['results']
        assert strict['stage'] == 'strict' and normal['stage'] == 'normal'
        assert '--trust=0' in strict['command']
        assert normal['command'] == ['lake', 'build', module] and normal['own_target_built']
        for result in (strict, normal):
            assert result['status'] == 'PASS' and result['exit_code'] == 0
            assert result['resource_stop'] is None and result['source_sha256'] == record['source_sha256']
            assert sha(ROOT / result['log']) == result['log_sha256']
            assert set(result['selected_axioms']) == set(record['selected_declarations'])
            for name, axioms in result['selected_axioms'].items():
                assert axioms is not None and set(axioms.replace(',', ' ').split()) <= STANDARD
                selected[name] = sorted(set(axioms.replace(',', ' ').split()))
            for line in (ROOT / result['log']).read_text().splitlines():
                if record['source'] + ':' in line and 'warning:' in line:
                    own_warnings.append({'module': module, 'stage': result['stage'], 'line': line})
        artifact = ROOT / '.lake/build/lib/lean' / Path(record['source']).with_suffix('.olean')
        assert sha(artifact) == normal['artifact_sha256']
        files.add(record['source'])
        for attempt in record['attempts']:
            assert sha(ROOT / attempt['log']) == attempt['log_sha256']
            files.add(attempt['log'])
            if snapshot := attempt.get('failed_source_snapshot'):
                assert sha(ROOT / snapshot) == attempt['failed_source_snapshot_sha256'] == attempt['source_sha256']
                files.add(snapshot)
        records[module] = record
    proof_manifest = 'research/JSP404_N4_R2_SHARED_REPLAY_SOURCE_MANIFEST_20261007.json'
    parity = 'research/JSP404_N4_R2_NAMED_LEAF_SOURCE_PARITY_20261007.json'
    audit = json.loads((ROOT / parity).read_text())
    assert audit['source_manifest_sha256'] == sha(ROOT / proof_manifest)
    assert audit['named_word_checks_in_source'] == 24698 and len(audit['blocks']) == 193
    connector_audit = 'research/JSP404_N4_R2_ALL_CONNECTOR_STATIC_AUDIT_20261007.json'
    connector = json.loads((ROOT / connector_audit).read_text())
    assert connector['status'] == 'STATIC_ONLY_NOT_KERNEL'
    for path, digest in connector['source_hashes'].items():
        assert sha(ROOT / path) == digest
    files.update([proof_manifest, parity,
                  connector_audit, 'tools/audit_n4_r2_all_connector_20261007.py',
                  'tools/export_n4_r2_named_leaf_replay_20261007.py',
                  'tools/audit_n4_r2_named_leaf_data_20261007.py',
                  'tools/check_n4_r2_replay_module_v2_20261007.py',
                  'tools/check_n4_r2_replay_isolated_20261007.py',
                  'tools/advance_n4_r2_replay_batch_20261007.py',
                  str(Path(__file__).resolve().relative_to(ROOT))])
    result = {'status': 'PASS_ALL24698_WORDS_SCALAR_BETWEEN_PROFILE',
              'kernel_all_words': True, 'scalar_between_terminal_ready': True,
              'original_problem_complete': False, 'actual_eight_point_consumer_in_this_receipt': False,
              'scope': 'GenericModel7 4; rowDefect0=2, rowDefect6=2, rows1..5 defect4. The actual model internally supplies triangle directions and complete row order. No caller word, catalog ID, accepted row, DBM oracle or goal bound.',
              'modules': records, 'selected_declarations': selected,
              'selected_count': len(selected), 'required_module_count': len(MODULES),
              'own_warning_occurrences': own_warnings,
              'publish_files': sorted(files), 'file_hashes': {p: sha(ROOT / p) for p in sorted(files)},
              'cycle_data_scope': 'Concrete local cycles are typed inside leaf modules; each checked word proves the chosen profile-cover branches. No claim that every unused diagnostic registry cycle is replayed.',
              'not_claimed': ['Outer01 profile', 'Original all-n theorem', 'Original lower theorem', 'Prize theorem']}
    output = ROOT / OUTPUT
    assert not output.exists(), 'Refusing to replace a final freeze receipt'
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'modules': len(MODULES),
                      'selected': len(selected), 'files': len(files), 'receipt_sha256': sha(output)}))


if __name__ == '__main__':
    main()
