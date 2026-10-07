#!/usr/bin/env python3
"""Package existing outer-left kernel receipts, refusing incomplete chains.

No compiler is run and no success is inferred from diagnostic enumeration.
Old between sources and receipts are read-only dependencies throughout.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CHECKPOINT = 'research/JSP404_N4_R2_OUTER_LEFT_CHECKPOINT_20261007.json'
CORE_RECEIPT = 'research/JSP404_N4_R2_OUTER_LEFT_REPLAY_SOUNDNESS_RECEIPT_20261007.json'
MANIFEST = 'research/JSP404_N4_R2_OUTER_LEFT_SOURCE_MANIFEST_20261007.json'
PARITY = 'research/JSP404_N4_R2_OUTER_LEFT_SOURCE_PARITY_20261007.json'
CONNECTOR = 'research/JSP404_N4_R2_OUTER_LEFT_ALL_CONNECTOR_STATIC_AUDIT_20261007.json'
OUTPUT = 'research/JSP404_N4_R2_OUTER_LEFT_REPLAY_FINAL_FREEZE_20261007.json'
BETWEEN_FREEZE = 'research/JSP404_N4_R2_BETWEEN_REPLAY_FINAL_FREEZE_20261007.json'
BETWEEN_SHA = '33f5b337e899b093faefb9d98ab14ef9f82e71bf68d432efb5c6345a9c8649d7'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
MODULES = (['Jsp000404.N4R2OuterLeftReplay'] +
           [f'Jsp000404.N4R2OuterLeftLeafCheckedShard{i:03d}' for i in range(193)] +
           ['Jsp000404.N4R2OuterLeftAllChecked', 'Jsp000404.N4R2OuterLeftTerminal'])


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_selected(source):
    text = (ROOT / source).read_text()
    namespace = re.search(r'^namespace\s+(\S+)', text, re.M).group(1)
    return [name if name.startswith('Jsp404.') else namespace + '.' + name
            for name in re.findall(r'^#print axioms\s+(\S+)', text, re.M)]


def main():
    args = argparse.ArgumentParser()
    args.add_argument('--check-only', action='store_true')
    options = args.parse_args()
    ledger = json.loads((ROOT / CHECKPOINT).read_text())
    missing = [m for m in MODULES if ledger['modules'].get(m, {}).get('status') != 'PASS']
    if missing:
        raise SystemExit(f'NOT_READY: {len(missing)} required targets lack PASS; first={missing[0]}')
    records, selected, files, warnings = {}, {}, set(), []

    def bind(path, digest=None):
        actual = sha(ROOT / path)
        assert digest is None or actual == digest, f'Hash mismatch: {path}'
        files.add(path)
        return actual

    def check_result(module, source, digest, names, result, log, log_sha):
        assert result['status'] == 'PASS' and result['exit_code'] == 0
        assert result['resource_stop'] is None and result['source_sha256'] == digest
        if result['stage'] == 'strict':
            assert '--trust=0' in result['command']
        else:
            assert result['command'] == ['lake', 'build', module] and result['own_target_built']
        assert set(result['selected_axioms']) == set(names)
        for name, axioms in result['selected_axioms'].items():
            ax = set(axioms.replace(',', ' ').split())
            assert ax <= STANDARD
            assert name not in selected or selected[name] == sorted(ax)
            selected[name] = sorted(ax)
        bind(log, log_sha)
        for line in (ROOT / log).read_text().splitlines():
            if source + ':' in line and 'warning:' in line:
                warnings.append({'module': module, 'stage': result['stage'], 'line': line})

    for module in MODULES:
        record = ledger['modules'][module]
        source, digest = record['source'], record['source_sha256']
        assert record['module'] == module
        assert source == module.replace('.', '/') + '.lean'
        assert record['selected_declarations'] == source_selected(source)
        bind(source, digest)
        assert [r['stage'] for r in record['results']] == ['strict', 'normal']
        for result in record['results']:
            check_result(module, source, digest, record['selected_declarations'], result,
                         result['log'], result['log_sha256'])
        artifact = ROOT / '.lake/build/lib/lean' / Path(source).with_suffix('.olean')
        assert sha(artifact) == record['results'][1]['artifact_sha256']
        for attempt in record['attempts']:
            bind(attempt['log'], attempt['log_sha256'])
            if snapshot := attempt.get('failed_source_snapshot'):
                bind(snapshot, attempt['failed_source_snapshot_sha256'])
                assert attempt['failed_source_snapshot_sha256'] == attempt['source_sha256']
        records[module] = record

    core = json.loads((ROOT / CORE_RECEIPT).read_text())
    bind(CORE_RECEIPT)
    source, digest = core['source']['path'], core['source']['sha256']
    assert core['module'] == 'Jsp000404.N4R2OuterLeftReplaySoundness'
    assert source == 'Jsp000404/N4R2OuterLeftReplaySoundness.lean'
    assert core['exports'] == source_selected(source) and len(core['exports']) == 9
    assert [core['strict0']['stage'], core['normal']['stage']] == ['strict', 'normal']
    bind(source, digest)
    for result in [core['strict0'], core['normal']]:
        check_result(core['module'], source, digest, core['exports'], result,
                     result['stdout']['path'], result['stdout']['sha256'])
    artifact = ROOT / '.lake/build/lib/lean' / Path(source).with_suffix('.olean')
    assert sha(artifact) == core['normal']['artifact_sha256']
    for item in core['verification_files'] + [core['research_note']]:
        bind(item['path'], item['sha256'])
    for dependency in core['dependency_sources']:
        assert sha(ROOT / dependency['path']) == dependency['sha256']

    manifest = json.loads((ROOT / MANIFEST).read_text())
    parity = json.loads((ROOT / PARITY).read_text())
    connector = json.loads((ROOT / CONNECTOR).read_text())
    assert manifest['complete_words'] == 24698 and len(manifest['blocks']) == 193
    for path, digest in manifest['source_hashes'].items():
        assert sha(ROOT / path) == digest
    assert parity['status'] == 'STATIC_SOURCE_AND_DECODER_PARITY_PASS_NOT_KERNEL'
    assert parity['manifest_sha256'] == sha(ROOT / MANIFEST)
    assert parity['words'] == 24698 and parity['contexts'] == 42788
    assert parity['input_sha256'] == manifest['input_sha256']
    assert sha(ROOT / manifest['input']) == manifest['input_sha256']
    assert sha(ROOT / manifest['generator']) == manifest['generator_sha256']
    assert parity['tool_sha256'] == sha(ROOT / 'tools/audit_n4_r2_outer_left_source_20261007.py')
    assert connector['status'] == 'STATIC_ONLY_NOT_KERNEL'
    for path, digest in connector['source_hashes'].items():
        assert sha(ROOT / path) == digest
    isolated_bindings = ledger.get('isolated_ledgers', {})
    for module, item in isolated_bindings.items():
        bind(item['path'], item['sha256'])
        isolated = json.loads((ROOT / item['path']).read_text())
        assert isolated['modules'][module] == ledger['modules'][module]
    assert sha(ROOT / BETWEEN_FREEZE) == BETWEEN_SHA
    for path in [MANIFEST, PARITY, CONNECTOR,
                 'tools/export_n4_r2_outer_left_replay_20261007.py',
                 'tools/audit_n4_r2_outer_left_source_20261007.py',
                 'tools/audit_n4_r2_outer_left_all_connector_20261007.py',
                 'tools/check_n4_r2_outer_left_module_20261007.py',
                 'tools/check_n4_r2_outer_left_isolated_20261007.py',
                 'tools/advance_n4_r2_outer_left_batch_20261007.py',
                 'tools/check_n4_r2_replay_module_v2_20261007.py',
                 'tools/check_six_symbolic_kernel_20261005.py',
                 'tools/audit_n4_r2_all_connector_20261007.py',
                 str(Path(__file__).resolve().relative_to(ROOT))]:
        bind(path)
    assert len(selected) == 397, f'Unexpected selected declaration count: {len(selected)}'
    result = {
        'status': 'PASS_ALL24698_WORDS_SCALAR_OUTER_LEFT_PROFILE',
        'kernel_all_words': True, 'scalar_outer_left_terminal_ready': True,
        'original_problem_complete': False,
        'actual_eight_point_consumer_in_this_receipt': False,
        'scope': 'GenericModel7 4; row1 defect2, rows2..6 defect4; row0 unrestricted. No HIGH, word, catalog ID, accepted row or goal bound is a caller input.',
        'modules': records, 'external_soundness_receipt': CORE_RECEIPT,
        'required_module_count': len(MODULES), 'external_soundness_module_count': 1,
        'reused_catalog_dependency_freeze': {'path': BETWEEN_FREEZE, 'sha256': BETWEEN_SHA,
                                           'module_count': 19, 'selected_count': 506},
        'isolated_ledger_bindings': isolated_bindings,
        'selected_declarations': selected, 'selected_count': len(selected),
        'own_warning_occurrences': warnings,
        'publish_files': sorted(files),
        'file_hashes': {path: sha(ROOT / path) for path in sorted(files)},
        'diagnostic_generator_input_local_only': {
            'path': manifest['input'], 'sha256': manifest['input_sha256'],
            'not_kernel_evidence': True,
            'all_required_cycle_literals_embedded_in_published_lean_sources': True},
        'not_claimed': ['Original all-n theorem', 'Original lower theorem', 'Prize theorem']}
    if not options.check_only:
        output = ROOT / OUTPUT
        assert not output.exists(), 'Refusing to replace a final freeze receipt'
        output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'modules': len(MODULES),
                      'selected': len(selected), 'files': len(files),
                      'receipt_written': not options.check_only}))


if __name__ == '__main__':
    main()
