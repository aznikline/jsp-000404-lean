"""Seal seven already checked standalone modules; no Lean/Git/shared edits.

Preparation never reads mutable prose. Finalization reads Root-updated prose and
publishes lossless output archives; original producer paths and bytes survive.
Only G01's verified five modules are allowed, not G02/03/04 or terminal drafts.
"""
from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import json
import re

HERE = '.lake/finalize_oct8_g01_general_standalone.py'
PLAN = '.lake/oct8-g01-general-standalone-prep.json'
STAGE = '.lake/oct8-g01-general-standalone-stage-files.json'
RECEIPT = 'research/JSP404_G01_GENERAL_STANDALONE_RECEIPT_20261008.json'
SCRIPT_COPY = 'verification/oct8-g01-general-standalone-review/finalize_receipt.py'
BASE = 'research/JSP404_UNIFORM_FOURMASK_INTEGRATION_RECEIPT_20261008.json'
HO = 'research/JSP404_ACTUAL_GENERAL_MAXIMAL_LOW_OBTUSE_EXCLUSION_RECEIPT_20261008.json'
ZERO = 'research/JSP404_ACTUAL_F17_UNIQUE_ZERO_CLASS_WEIGHT_RECEIPT_20261008.json'
G01 = Path('verification/oct8-six-weak-remainder-g01')
DOCS = ['notes/STATUS.md', 'research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOT_AUDIT = ['Jsp000404.lean', 'verification/oct5-review/ProofAudit.lean']
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
FIXED = {
    BASE: 'e457ab3ff5214d813963efe5964fd35ff40f35cfa061c06766c678050ee1d727',
    HO: '624b1922da70526920c6a1312f125ca79740e25d1fda9887595c64d1c8cd74dd',
    ZERO: '5d3c8fadb53a0cfcff8cd616b6745580dc0184d7c0174401144930dfafd38bf0',
    str(G01/'RECEIPT.md'): 'f4a3385c8abf29136f9d83164eced89b905b3ac7a83d39901da93ca8b45216a3',
    str(G01/'final-result.json'): '9ef3e48f05a4a227b43349de905675f6e0f955f53ba13594f8771cb1a3bbfc52',
}


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def read(p):
    return json.loads(Path(p).read_text())


def hashes(mapping):
    for p, h in mapping.items():
        assert sha(p) == h, ('changed frozen file', p)


def printed(p, names):
    matches = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", Path(p).read_text(), re.S))
    out = {}
    for n in names:
        assert n in matches, n
        ax = {x.strip() for x in matches[n].split(',') if x.strip()}
        assert ax <= STANDARD, (n, ax)
        out[n] = sorted(ax)
    return out


def archives_for(files):
    projected, records = set(files), []
    for p in sorted(files):
        if Path(p).suffix not in ['.txt', '.out']:
            continue
        raw = Path(p).read_bytes()
        if 'normal' not in Path(p).name and not any(re.search(rb'[ \t]+$', line) for line in raw.splitlines()):
            continue
        pub = p + '.gz'
        zipped = Path(pub).read_bytes() if Path(pub).exists() else gzip.compress(raw, mtime=0)
        assert gzip.decompress(zipped) == raw
        projected.remove(p)
        projected.add(pub)
        records.append({'raw_path': p, 'raw_sha256': sha(p), 'published_path': pub,
                        'published_sha256': hashlib.sha256(zipped).hexdigest(), 'encoding': 'gzip',
                        'exact_original_byte_restoration': True})
    return projected, records


def inputs():
    hashes(FIXED)
    base, ho, zero = read(BASE), read(HO), read(ZERO)
    assert (base['default_build_jobs'], base['composed_standard_axiom_count']) == (10909, 2256)
    assert sha(ROOT_AUDIT[0]) == base['root_sha256']
    assert sha(ROOT_AUDIT[1]) == base['audit_sha256']
    guards = dict(base['preserved_prior_sha256'])
    guards.update(base['import_closure_source_sha256'])
    guards.update({p: h for p, h in base['publication_file_sha256'].items() if p not in DOCS})
    hashes(guards)
    hashes(base['paper_only_sha256'])
    files, modules, passed, failed, archives = set(), {}, [], [], []
    for d in [ho, zero]:
        hashes(d['publication_file_sha256'])
        source = d['source']
        assert sha(source['path']) == source['sha256']
        modules[d['module']] = {'source': source['path'], 'source_sha256': source['sha256'], 'selected': d['exports']}
        files.update(d['publication_file_whitelist'])
        assert len(d['failed_attempts']) == 1 and d['mathematical_premises_changed'] is False
        for stage in ['strict0', 'normal']:
            r = d[stage]
            assert r['exit_code'] == 0 and not r['resource_stop']
            assert sha(r['log']) == r['log_sha256']
            assert sha(r['source_snapshot']) == r['source_snapshot_sha256'] == source['sha256']
            ax = printed(r['log'], d['exports'])
            if stage == 'strict0':
                assert '--trust=0' in r['command']
            else:
                assert r['own_target_built'] is True
                text = Path(r['log']).read_text()
                assert 'Built ' + d['module'] in text and 'Build completed successfully' in text
            passed.append({'module': d['module'], 'stage': stage, 'producer_run': r, 'selected_standard_axioms': ax})
        for r in d['failed_attempts']:
            assert r['status'] == 'NOT_PROVED' and r['exit_code'] != 0 and not r['resource_stop']
            assert sha(r['log']) == r['log_sha256']
            assert sha(r['source_snapshot']) == r['source_snapshot_sha256'] == r['source_sha256']
            failed.append({'module': d['module'], **r})
        for a in d['lossless_stdout_archives']:
            raw, pub = a['raw_path'], a['published_gzip']
            assert sha(raw) == a['raw_sha256'] and sha(pub) == a['gzip_sha256']
            assert gzip.decompress(Path(pub).read_bytes()) == Path(raw).read_bytes()
            archives.append({'raw_path': raw, 'raw_sha256': sha(raw), 'published_path': pub,
                             'published_sha256': sha(pub), 'encoding': 'gzip', 'exact_original_byte_restoration': True})
    final, cp = read(G01/'final-result.json'), read(G01/'compile-plan.json')
    assert final['status'] == 'PASS_GROUP01_SIXTEEN_ONLY' and final['selected_count'] == 114
    assert final['compiler_attempts'] == 10 and not final['local_failed_candidates'] and not final['local_source_repairs']
    assert final['catalog_indices'] == list(range(1, 17)) and final['kernel_words_with_previous_group00'] == 20
    assert not final['all62_complete'] and not final['complete_no_word_A_proved'] and not final['complete_no_word_B_proved']
    assert final['compile_plan_sha256'] == sha(G01/'compile-plan.json')
    assert final['runner_sha256'] == sha(G01/'check.py')
    hashes(final['protected_existing_sources'])
    guards.update(final['protected_existing_sources'])
    files.update(str(G01/p) for p in ['RECEIPT.md', 'compile-plan.json', 'final-result.json', 'check.py'])
    for module in cp['topological_order']:
        f, c = final['modules'][module], cp['modules'][module]
        assert sha(f['source']) == f['source_sha256'] == c['initial_source_sha256'] == c['approved_source_sha256']
        modules[module] = {'source': f['source'], 'source_sha256': f['source_sha256'], 'selected': c['selected']}
        files.add(f['source'])
        checkpoint = G01/module.split('.')[-1]/'checkpoint.json'
        assert sha(checkpoint) == f['checkpoint_sha256']
        files.add(str(checkpoint))
        assert len(read(checkpoint)['attempts']) == 2
        for stage in ['strict', 'normal']:
            r = f[stage]
            assert r['status'] == 'PASS' and r['exit_code'] == 0 and not r['resource_stop']
            assert sha(r['stdout']) == r['stdout_sha256']
            assert sha(r['source_snapshot']) == r['source_snapshot_sha256'] == f['source_sha256']
            ax = printed(r['stdout'], c['selected'])
            assert r['selected_standard_axioms_gate']
            if stage == 'strict':
                assert '--trust=0' in r['command']
            else:
                assert r['own_target_built'] is True
                text = Path(r['stdout']).read_text()
                assert 'Built ' + module in text and 'Build completed successfully' in text
            passed.append({'module': module, 'stage': stage, 'producer_run': r, 'selected_standard_axioms': ax})
            files.update([r['stdout'], r['source_snapshot']])
    selected = [n for d in modules.values() for n in d['selected']]
    assert len(modules) == 7 and len(selected) == len(set(selected)) == 116
    assert len(passed) == 14 and len(failed) == 2
    allowed = {**guards, **{d['source']: d['source_sha256'] for d in modules.values()}}
    closure, pending = set(), [d['source'] for d in modules.values()]
    while pending:
        p = pending.pop()
        if p in closure:
            continue
        assert p in allowed and sha(p) == allowed[p], ('unverified dependency', p)
        closure.add(p)
        for m in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$', Path(p).read_text(), re.M):
            pending.append(m.replace('.', '/') + '.lean')
    assert all(not p.startswith('.lake/') and not p.endswith(('.olean', '.ilean', '.trace', '.log')) for p in files)
    assert not any('/corpus/' in p or any(x in p.lower() for x in ['group02', 'group03', 'group04', 'z1apex']) for p in files)
    return base, modules, selected, files, guards, passed, failed, archives, final


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    base, modules, selected, files, guards, passed, failed, archives, final = inputs()
    projected, projected_archives = archives_for(files)
    if args.prepare_only:
        plan = {'status': 'READY_STANDALONE_ONLY_DEFAULT2256_UNCHANGED', 'new_module_count': 7,
                'new_selected_count': 116, 'modules': modules, 'new_selected': selected,
                'input_file_sha256': {p: sha(p) for p in sorted(files)}, 'producer_receipt_sha256': FIXED,
                'finalizer_sha256': sha(HERE), 'prospective_lossless_archives': projected_archives,
                'prospective_publication_paths': sorted(projected | {RECEIPT, SCRIPT_COPY} | set(DOCS)),
                'default_gate_unchanged': {'jobs': 10909, 'verified': 2256, 'default_selected': 2249, 'explicit_helpers': 7},
                'root_sha256': base['root_sha256'], 'audit_sha256': base['audit_sha256'], 'docs_not_read': True,
                'kernel_word_scope': 'G01 sixteen words plus publishedG00 four =20/62, no complete A/B terminal',
                'excluded': ['G02/03/04 and finalthree SOURCE_ONLY', 'Z1Apex pending paper', 'Any unified2372 audit claim']}
        Path(PLAN).write_text(json.dumps(plan, indent=2) + '\n')
        print(json.dumps({'status': 'READY', 'plan': PLAN, 'sha256': sha(PLAN), 'input_files': len(files),
                          'projected_publication_files': len(plan['prospective_publication_paths']), 'new_modules': 7,
                          'standalone_selected': 116, 'new_gzip_archives': len(projected_archives), 'default_verified': 2256}))
        return
    plan = read(PLAN)
    assert plan['finalizer_sha256'] == sha(HERE) and plan['modules'] == modules
    hashes(plan['input_file_sha256'])
    assert plan['prospective_lossless_archives'] == projected_archives
    assert plan['prospective_publication_paths'] == sorted(projected | {RECEIPT, SCRIPT_COPY} | set(DOCS))
    Path(SCRIPT_COPY).parent.mkdir(parents=True, exist_ok=True)
    if Path(SCRIPT_COPY).exists():
        assert Path(SCRIPT_COPY).read_bytes() == Path(HERE).read_bytes()
    else:
        Path(SCRIPT_COPY).write_bytes(Path(HERE).read_bytes())
    for a in projected_archives:
        p = Path(a['published_path'])
        if not p.exists():
            p.write_bytes(gzip.compress(Path(a['raw_path']).read_bytes(), mtime=0))
        assert sha(p) == a['published_sha256']
    files = projected | {RECEIPT, SCRIPT_COPY} | set(DOCS)
    record = {'recorded_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'status': 'SCOPED_STANDALONE_PASS_G01_GENERAL_HO_UNIQUE_ZERO_CLASS', 'original_problem_complete': False,
              'publication_base_commit_reported_by_root': 'fea913f', 'base_default_receipt': {'path': BASE, 'sha256': FIXED[BASE]},
              'default_gate_unchanged': plan['default_gate_unchanged'], 'root_sha256': base['root_sha256'],
              'audit_sha256': base['audit_sha256'], 'new_module_count': 7, 'new_selected_count': 116,
              'modules': modules, 'new_selected': selected, 'producer_receipt_sha256': FIXED,
              'selected_verification_scope': 'Independent producer strict --trust=0 and genuine own-target Lake builds only; no new combined/root2372 gate.',
              'successful_checks': passed, 'successful_check_count': 14, 'failed_NOT_PROVED_attempts': failed,
              'preserved_prior_sha256': guards, 'paper_only_sha256': base['paper_only_sha256'],
              'lossless_stdout_archives': archives + projected_archives, 'shared_document_sha256': {p: sha(p) for p in DOCS},
              'kernel_word_scope': {'new_catalog_indices': final['catalog_indices'], 'new_masks': final['masks'],
                                    'new_words': 16, 'with_published_group00': 20, 'catalog_total': 62, 'all62_complete': False,
                                    'complete_no_word_A_proved': False, 'complete_no_word_B_proved': False},
              'scope': ['G01: five verified unchanged modules/114 public declarations for sixteen new catalog words, internally producing actual row orders and replaying A/B certificates. Total kernel coverage with publishedG00 is20/62.',
                        'GeneralHO: n>=4 original LOW minimum Model, original B/C scores n-2, actual B obtuse angle>pi-2lambda and distinct C nonacute angle>=2lambda implyFalse. No caller clumps/gap/budget.',
                        'UniqueZeroClass: original LOW4 minimum Model with a unique original zero and an original score-one interior point internally supplies actual3class Data. Original class masses sum15, each>=3, classes not containing the zero>=4, pairs>=7 and each<=8; a singleton original heavy remains allowed.'],
              'warning_policy': 'All final producer-owned warning counts0; inherited output is retained verbatim. GeneralHO normal463; UniqueZeroClass and G01 warnings remain in original output. No all-output-warning-free claim.',
              'failure_policy': 'Actual GeneralHO0a294 and UniqueZero1f04 failed sources/raw remain NOT_PROVED. Final910e12/a862 are distinct checked bytes; no reconstructed failures or stripped output.',
              'not_proved': plan['excluded'] + ['Complete weak A/B closures or actualF22/fullR2', 'Original wholeF17 or arbitrary-N lower/prize completion'],
              'publication_file_whitelist': sorted(files), 'publication_file_sha256': {p: sha(p) for p in sorted(files) if p != RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(record, indent=2) + '\n')
    Path(STAGE).write_text(json.dumps(sorted(files), indent=2) + '\n')
    print(json.dumps({'receipt': RECEIPT, 'sha256': sha(RECEIPT), 'files': len(files), 'stage_manifest': STAGE,
                      'standalone_selected': 116, 'default_verified_unchanged': 2256, 'staged': False}))


if __name__ == '__main__':
    main()
