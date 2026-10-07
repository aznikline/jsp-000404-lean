"""Freeze the new composed checks without rerunning Lean/Git or editing prose.

Only the five checked group00 modules and General's exact producer whitelist are
new producer publication files. Earlier standalone evidence stays frozen and is
referenced by hash. Remaining58, group01 and generation-only units are excluded.
"""
from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import json
import re

PREP = '.lake/oct8-uniform-fourmask-prep.json'
PLAN = '.lake/oct8-uniform-fourmask-publication-plan.json'
RECEIPT = 'research/JSP404_UNIFORM_FOURMASK_INTEGRATION_RECEIPT_20261008.json'
STAGE = '.lake/oct8-uniform-fourmask-stage-files.json'
OUT = Path('verification/oct8-uniform-fourmask-review')
FOUR = Path('verification/oct8-six-weak-all-four')
GENERAL = 'research/JSP404_ACTUAL_GENERAL_MAXIMAL_LOW_CLUMP_WEIGHT_RECEIPT_20261008.json'
BASE = 'research/JSP404_F18_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
STANDALONE = 'research/JSP404_STANDALONE_LOW4_WEAK_PILOTS_RECEIPT_20261008.json'
REDUCER = 'research/JSP404_LOW4_F17_CRITICAL_REDUCTION_STANDALONE_RECEIPT_20261008.json'
DOCS = ['notes/STATUS.md', 'research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOT_AUDIT = ['Jsp000404.lean', 'verification/oct5-review/ProofAudit.lean']
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def read(p):
    return json.loads(Path(p).read_text())


def hashes(mapping):
    for p, h in mapping.items():
        assert sha(p) == h, ('changed frozen file', p)


def printed(p, names):
    matches = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", Path(p).read_text(), re.S))
    for n in names:
        assert n in matches and {x.strip() for x in matches[n].split(',') if x.strip()} <= STANDARD, n


def inputs():
    prep = read(PREP)
    hashes(prep['producer_receipt_sha256'])
    hashes(prep['preserved_prior_sha256'])
    hashes(prep['new_source_sha256'])
    hashes(prep['import_closure_source_sha256'])
    assert sha(ROOT_AUDIT[0]) == prep['root_after_sha256']
    assert sha(ROOT_AUDIT[1]) == prep['audit_after_sha256']
    assert len(prep['modules']) == 17 and len(set(prep['new_selected'])) == 53
    names = re.findall(r'^#print axioms (\S+)', Path(ROOT_AUDIT[1]).read_text(), re.M)
    assert len(names) == len(set(names)) == 2257 and set(prep['new_selected']) <= set(names)
    general, four, cp = read(GENERAL), read(FOUR/'final-result.json'), read(FOUR/'compile-plan.json')
    hashes(general['publication_file_sha256'])
    files = set(general['publication_file_whitelist'])
    files.update(str(FOUR/p) for p in ['RECEIPT.md', 'compile-plan.json', 'final-result.json', 'check.py'])
    assert four['status'] == 'PASS_FOUR_MASKS_ONLY' and four['selected_count'] == 30
    assert four['masks'] == [0, 202, 472, 1023] and four['catalog_indices'] == [0, 17, 26, 61]
    assert len(four['remaining_catalog_indices']) == 58 and not four['all62_generated']
    assert not four['complete_no_word_A_proved'] and not four['complete_no_word_B_proved']
    assert not four['local_failures'] and not four['local_source_repairs']
    assert four['compile_plan_sha256'] == sha(FOUR/'compile-plan.json')
    assert four['runner_sha256'] == sha(FOUR/'check.py')
    hashes(four['protected_existing_sources'])
    for module, record in four['modules'].items():
        assert sha(record['source']) == record['source_sha256']
        files.add(record['source'])
        checkpoint = FOUR/module.split('.')[-1]/'checkpoint.json'
        assert sha(checkpoint) == record['checkpoint_sha256']
        files.add(str(checkpoint))
        for kind in ['strict', 'normal']:
            r = record[kind]
            assert r['status'] == 'PASS' and r['exit_code'] == 0 and not r['resource_stop']
            assert r['selected_standard_axioms_gate']
            assert sha(r['stdout']) == r['stdout_sha256']
            assert sha(r['source_snapshot']) == r['source_snapshot_sha256'] == record['source_sha256']
            printed(r['stdout'], cp['modules'][module]['selected'])
            if kind == 'normal':
                assert r['own_target_built'] is True
                text = Path(r['stdout']).read_text()
                assert 'Built ' + module in text and 'Build completed successfully' in text
            else:
                assert '--trust=0' in r['command']
            files.update([r['stdout'], r['source_snapshot']])
    for kind in ['strict0', 'normal']:
        r = general[kind]
        assert r['exit_code'] == 0 and not r['resource_stop']
        assert sha(r['log']) == r['log_sha256']
        assert sha(r['source_snapshot']) == r['source_snapshot_sha256'] == general['source']['sha256']
        printed(r['log'], general['exports'])
        if kind == 'normal':
            assert r['own_target_built'] is True
            text = Path(r['log']).read_text()
            assert 'Built ' + general['module'] in text and 'Build completed successfully' in text
    # Earlier public sources and receipts are unchanged; mutable prose advances.
    for receipt in [BASE, STANDALONE, REDUCER]:
        d = read(receipt)
        hashes({p: h for p, h in d['publication_file_sha256'].items() if p not in DOCS + ROOT_AUDIT})
    assert all(not p.startswith('.lake/') and not p.endswith(('.log', '.olean', '.ilean', '.trace')) for p in files)
    assert not any('remainder' in p.lower() or 'group01' in p.lower() or '/corpus/' in p for p in files)
    return prep, general, four, files


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    prep, general, four, files = inputs()
    if args.prepare_only:
        plan = {'status': 'PRODUCERS_READY_COMPOSED_GATES_PENDING', 'new_module_count': 17,
                'new_selected_count': 53, 'requested_verified': 2256, 'requested_default': 2249,
                'new_selected': prep['new_selected'], 'producer_files': sorted(files),
                'producer_file_sha256': {p: sha(p) for p in sorted(files)},
                'root_sha256': prep['root_after_sha256'], 'audit_sha256': prep['audit_after_sha256'],
                'docs_not_read': True, 'generation_only_provenance_not_published': True,
                'remaining58_and_group01_excluded': True}
        Path(PLAN).write_text(json.dumps(plan, indent=2) + '\n')
        print(json.dumps({'status': 'READY', 'plan': PLAN, 'sha256': sha(PLAN), 'producer_files': len(files), 'verified_requested': 2256}))
        return
    plan = read(PLAN)
    hashes(plan['producer_file_sha256'])
    full, audit, gates = read(OUT/'full.json'), read(OUT/'audit.json'), read(OUT/'gates.json')
    for r in [full, audit]:
        assert r['exit_code'] == 0 and not r['rss_cap_killed'] and not r['timeout_killed']
        assert not r.get('parallel_lean_cap_killed') and r['max_global_lean_count'] <= 1
        assert sha(r['stdout']) == r['stdout_sha256']
    assert gates[0]['exit_code'] == 0 and gates[0]['declaration_count'] == 2256 and not gates[0]['failures']
    assert gates[1]['exit_code'] == 1 and gates[1]['failures'] == [{'declaration': 'Jsp404.sendov_lower', 'unexpected_axioms': ['sorryAx']}]
    for r in gates:
        assert sha(r['stdout']) == r['stdout_sha256']
    axioms = read(gates[0]['stdout'])['axioms']
    assert all(n in axioms and set(axioms[n]) <= STANDARD for n in prep['new_selected'])
    jobs = int(re.search(r'Build completed successfully \((\d+) jobs\)', Path(full['stdout']).read_text()).group(1))
    files.update(DOCS + ROOT_AUDIT)
    files.update(str(OUT/p) for p in ['full.json', 'full.stdout.txt', 'audit.json', 'audit.stdout.txt', 'gates.json', 'verified-gate.json', 'root-gate.json'])
    for src, name in [('.lake/run_oct8_uniform_fourmask_bundle.py', 'run_checks.py'),
                      ('.lake/check_oct8_uniform_fourmask_bundle_gates.py', 'check_gates.py'),
                      ('.lake/finalize_oct8_uniform_fourmask_bundle.py', 'finalize_receipt.py')]:
        dst = OUT/name
        if dst.exists():
            assert dst.read_bytes() == Path(src).read_bytes()
        else:
            dst.write_bytes(Path(src).read_bytes())
        files.add(str(dst))
    archives = []
    for a in general['lossless_stdout_archives']:
        raw, pub = a['raw_path'], a['published_gzip']
        assert sha(raw) == a['raw_sha256'] and sha(pub) == a['gzip_sha256']
        assert gzip.decompress(Path(pub).read_bytes()) == Path(raw).read_bytes()
        archives.append({'raw_path': raw, 'raw_sha256': sha(raw), 'published_path': pub,
                         'published_sha256': sha(pub), 'encoding': 'gzip', 'exact_original_byte_restoration': True})
    for p in sorted(files):
        q = Path(p)
        if q.suffix not in ['.txt', '.out']:
            continue
        raw = q.read_bytes()
        if 'normal' not in q.name and 'full' not in q.name and not any(re.search(rb'[ \t]+$', line) for line in raw.splitlines()):
            continue
        pub = p + '.gz'
        if Path(pub).exists():
            assert gzip.decompress(Path(pub).read_bytes()) == raw
        else:
            Path(pub).write_bytes(gzip.compress(raw, mtime=0))
        archives.append({'raw_path': p, 'raw_sha256': sha(p), 'published_path': pub,
                         'published_sha256': sha(pub), 'encoding': 'gzip', 'exact_original_byte_restoration': True})
        files.remove(p)
        files.add(pub)
    files.add(RECEIPT)
    r = {'recorded_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'status': 'SCOPED_PASS_COMPOSED_LOW_SUPPORT_AND_FOUR_WEAK_MASKS', 'original_problem_complete': False,
         'publication_base_commit_reported_by_root': prep['publication_base_commit'],
         'producer_receipt_sha256': prep['producer_receipt_sha256'],
         'new_modules': prep['modules'], 'new_selected': prep['new_selected'], 'new_selected_count': 53,
         'new_module_count': 17, 'composed_standard_axiom_count': 2256, 'default_root_selected_count': 2249,
         'existing_explicit_helpers': 7, 'default_build_jobs': jobs, 'full_build': full,
         'composed_trust_zero_audit': audit, 'standard_axiom_gate': gates[0], 'original_root_negative_gate': gates[1],
         'source_sha256': prep['new_source_sha256'], 'preserved_prior_sha256': prep['preserved_prior_sha256'],
         'import_closure_source_sha256': prep['import_closure_source_sha256'], 'paper_only_sha256': prep['paper_only_sha256'],
         'root_sha256': sha(ROOT_AUDIT[0]), 'audit_sha256': sha(ROOT_AUDIT[1]),
         'shared_document_sha256': {p: sha(p) for p in DOCS}, 'lossless_stdout_archives': archives,
         'fourmask_scope': {'masks': four['masks'], 'catalog_indices': four['catalog_indices'],
                            'remaining_catalog_indices': four['remaining_catalog_indices'], 'all62_proved': False,
                            'complete_no_word_A_proved': False, 'complete_no_word_B_proved': False},
         'scope': [prep['scope'],
                   'General n>=4: original LOW minimum Model plus an original maximal row score n-2 gives zero observer gain; actual nonacute witness supplies actual two-clump cardinality/weight bounds.',
                   'Previously standalone Reducer1 and support20 are now loaded by default and included in the2256 composed gate. Earlier producer evidence is referenced unchanged.',
                   'Fourmask30 checks A/B on masks000/202/472/1023 with actual row orders. No caller profile/cycle/row-order oracle; final complete A/B terminals remain open.'],
         'warning_policy': 'All new producer-owned warnings are0; inherited General normal463 and fourmask/raw/composed warnings remain unchanged. No all-output-warning-free claim.',
         'warning_headers': {k: len(re.findall(r"^warning:", Path(v['stdout']).read_text(), re.M)) for k, v in [('full', full), ('audit', audit)]},
         'failure_policy': 'New fourmask and General producers have no failed attempts. Three prior weak pilot failures and the Reducer API failure remain frozen in the earlier public receipts/source/raw records; none is counted as PASS.',
         'excluded': ['Remaining58/group01 and generated-only units', 'New paper-only work', 'Complete weak A/B or actualF22/fullR2 capacity', 'Original wholeF17 exclusion', 'Original arbitrary-N lower/prize completion'],
         'publication_file_whitelist': sorted(files), 'publication_file_sha256': {p: sha(p) for p in sorted(files) if p != RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r, indent=2) + '\n')
    Path(STAGE).write_text(json.dumps(sorted(files), indent=2) + '\n')
    print(json.dumps({'receipt': RECEIPT, 'sha256': sha(RECEIPT), 'files': len(files), 'stage_manifest': STAGE,
                      'full_jobs': jobs, 'verified': 2256, 'staged': False}))


if __name__ == '__main__':
    main()
