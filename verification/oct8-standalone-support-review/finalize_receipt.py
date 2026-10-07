"""Seal already checked standalone evidence; never run Lean, Git, or edit shared sources.

--prepare-only writes a private exact input plan without reading mutable prose.
The final run reads Root-updated prose, archives output losslessly, and writes the
new receipt plus exact stage list. Prior producer records retain original paths.
"""
from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import json
import re

PLAN = '.lake/oct8-standalone-support-prep.json'
RECEIPT = 'research/JSP404_STANDALONE_LOW4_WEAK_PILOTS_RECEIPT_20261008.json'
STAGE = '.lake/oct8-standalone-support-stage-files.json'
HERE = '.lake/finalize_oct8_standalone_support.py'
PUBLISHED_SCRIPT = 'verification/oct8-standalone-support-review/finalize_receipt.py'
BASE = 'research/JSP404_F18_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
BASE_SHA = 'd55145fb2b7bbf2dc61d67eb2f8c09fb059a556c02bbf9a9f0503f231fe3fc70'
WB = 'research/JSP404_LOW4_WHOLE_BAND_FIXED_CARD_RECEIPT_20261008.json'
OBS = 'research/JSP404_ACTUAL_F17_POSITIVE_OBSERVER_ZERO_GAIN_RECEIPT_20261008.json'
HO = 'verification/oct8-f17-observer-ho-batch/ho-receipt.json'
WEAK = Path('verification/oct8-six-weak-pilots-local')
DEPENDENCY = 'research/JSP404_LOW4_F17_CRITICAL_REDUCTION_STANDALONE_RECEIPT_20261008.json'
PAPER = 'research/JSP404_F17_MANDATORY_SELECTION_BOUNDED_OCT8.md'
FIXED = {
    BASE: BASE_SHA,
    WB: 'ac03550fdb4e2ed5dffb772afc84e0d84e133764d440172adbbd3e6346f4e36c',
    OBS: 'adce61c6e7eb2321f86dc4186f87d70a36bf65d2d64d33dd83fe21d9d5241940',
    HO: '84fc3e9edc61e8e680191de247429d4edb2dc52db02c8d753bda35c4b7553509',
    str(WEAK/'manifest.json'): '454c5d3320da83b2feb27a4f19a78b2ba6611c2ec82bdd4cb39184dc9a41baba',
    str(WEAK/'RECEIPT.md'): '396605dc173e4e5aef9df2e1fa1d66e441a4b337766fdea18b11430f2f99452a',
    DEPENDENCY: 'b0e5273e31b0db5c204cb22e455e2b521e621aaa195c7f5ff59393bf5970e732',
    PAPER: 'bb3900338e75c512da3b7ad57438d6a843183192d763ecd6d0cf613ef68c4acb',
}
DOCS = ['notes/STATUS.md', 'research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def read(p):
    return json.loads(Path(p).read_text())


def check_hashes(mapping):
    for p, h in mapping.items():
        assert sha(p) == h, ('changed frozen file', p)


def meta(m):
    assert sha(m['path']) == m['sha256'], m['path']


def printed(raw, selected):
    axioms = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", raw.decode(), re.S))
    for n in selected:
        assert n in axioms, ('missing printed declaration', n)
        assert {x.strip() for x in axioms[n].split(',') if x.strip()} <= STANDARD, n
    return {n: sorted(x.strip() for x in axioms[n].split(',') if x.strip()) for n in selected}


def archive_projection(files):
    projected = set(files)
    archives = []
    for p in sorted(files):
        q = Path(p)
        if q.suffix not in ['.txt', '.out']:
            continue
        raw = q.read_bytes()
        if 'normal' not in q.name and not any(re.search(rb'[ \t]+$', line) for line in raw.splitlines()):
            continue
        pub = p + '.gz'
        encoded = Path(pub).read_bytes() if Path(pub).exists() else gzip.compress(raw, mtime=0)
        assert gzip.decompress(encoded) == raw
        archives.append({'raw_path': p, 'raw_sha256': sha(p), 'published_path': pub,
                         'published_sha256': hashlib.sha256(encoded).hexdigest(),
                         'encoding': 'gzip', 'exact_byte_restoration': True})
        projected.remove(p)
        projected.add(pub)
    return projected, archives


def run_check(module, kind, run, selected, source_hash, log_key='stdout'):
    assert run['exit_code'] == 0 and not run.get('resource_stop')
    assert not run.get('guard', {}).get('guard_reason')
    if log_key == 'log':
        p, h = run['log'], run['log_sha256']
        snap, sh = run['source_snapshot'], run['source_snapshot_sha256']
    elif log_key == 'observer':
        p, h = run['actual_stdout']['path'], run['actual_stdout']['sha256']
        snap, sh = run['actual_source_snapshot']['path'], run['actual_source_snapshot']['sha256']
    else:
        p, h = run['stdout']['path'], run['stdout']['sha256']
        snap, sh = run['exact_source_snapshot']['path'], run['exact_source_snapshot']['sha256']
    assert sha(p) == h and sha(snap) == sh == source_hash
    raw = Path(p).read_bytes()
    ax = printed(raw, selected)
    if kind == 'normal':
        assert run.get('own_target_built', run.get('genuine_own_target_built')) is True
        assert 'Built ' + module in raw.decode() and 'Build completed successfully' in raw.decode()
    return {'module': module, 'kind': kind, 'original_stdout': p, 'original_stdout_sha256': h,
            'source_sha256': source_hash, 'selected_axioms': ax,
            'genuine_own_target_built': kind == 'normal'}


def inputs():
    check_hashes(FIXED)
    base, wb, obs, ho = map(read, [BASE, WB, OBS, HO])
    assert (base['default_build_jobs'], base['composed_standard_axiom_count']) == (10892, 2203)
    assert sha('Jsp000404.lean') == base['root_sha256']
    assert sha('verification/oct5-review/ProofAudit.lean') == base['audit_sha256']
    guards = {}
    for k in ['preserved_tracked_lean_sha256', 'preserved_old2200_source_sha256', 'source_sha256',
              'import_closure_source_sha256', 'paper_only_sha256', 'old2200_receipt_and_log_hashes']:
        guards.update(base[k])
    guards.update({p: h for p, h in base['publication_file_sha256'].items() if p not in DOCS})
    prior = read(DEPENDENCY)
    guards[prior['source']] = prior['source_sha256']
    guards.update({p: h for p, h in prior['publication_file_sha256'].items() if p not in DOCS})
    check_hashes(guards)
    check_hashes(wb['publication_file_sha256'])
    files = set(wb['publication_file_whitelist']) | set(obs['publication_whitelist'])
    files.update(['Jsp000404/ActualF17ObtuseHeavyExclusion.lean', HO,
                  'verification/oct8-f17-observer-ho-batch/run.py',
                  'verification/oct8-f17-observer-ho-batch/ho-selected-names.txt',
                  'verification/oct8-f17-observer-ho-batch/ho-scope.md'])
    modules, runs = {}, []
    for d, names, mode in [(wb, wb['exports'], 'log'), (obs, obs['selected_exports'], 'observer'), (ho, ho['exports'], 'stdout')]:
        meta(d['source'])
        module, source = d['module'], d['source']
        modules[module] = {'source': source['path'], 'source_sha256': source['sha256'], 'selected': names}
        stages = d['runs'] if mode == 'observer' else [d['strict0'], d['normal']]
        for j, r in enumerate(stages):
            runs.append(run_check(module, 'strict' if j == 0 else 'normal', r, names, source['sha256'], mode))
            if mode == 'stdout':
                files.update([r['stdout']['path'], r['exact_source_snapshot']['path']])
    manifest, final = read(WEAK/'manifest.json'), read(WEAK/'final-result.json')
    assert manifest['status'] == final['status'] == 'PASS_PILOT_472_ONLY'
    assert final['manifest_sha256'] == sha(WEAK/'manifest.json')
    assert final['runner_sha256'] == sha(WEAK/'check.py')
    assert final['total_compiler_attempts'] == 17 and len(final['failed_attempts']) == 3
    assert not final['typed_all62_verified'] and not final['all10_dispatch_Lean_verified']
    assert not manifest['all62_generated'] and manifest['pilot_mask'] == 472
    check_hashes(manifest['protected_existing_sources'])
    guards.update(manifest['protected_existing_sources'])
    files.update(str(WEAK/p) for p in ['READY.md', 'RECEIPT.md', 'manifest.json', 'final-result.json', 'check.py'])
    failed = []
    for module in manifest['topological_order']:
        m, f = manifest['modules'][module], final['modules'][module]
        assert m['approved_source_sha256'] == f['source_sha256'] == sha(m['source'])
        modules[module] = {'source': m['source'], 'source_sha256': f['source_sha256'], 'selected': m['selected']}
        files.add(m['source'])
        cp = WEAK/module.split('.')[-1]/'checkpoint.json'
        assert sha(cp) == f['checkpoint_sha256']
        files.add(str(cp))
        attempts = read(cp)['attempts']
        for r in attempts:
            p, snap = r['stdout'], r['source_snapshot']
            assert sha(p) == r['stdout_sha256'] and sha(snap) == r['source_snapshot_sha256'] == r['source_sha256']
            assert r['resource_stop'] is None
            files.update([p, snap])
            if r['status'] != 'PASS':
                assert r['status'] == 'NOT_PROVED' and r['exit_code'] != 0
                failed.append({'module': module, **r})
                continue
            assert r['exit_code'] == 0 and r['source_sha256'] == f['source_sha256']
            assert r['selected_standard_axioms_gate']
            raw = Path(p).read_bytes()
            ax = printed(raw, m['selected'])
            if r['stage'] == 'normal':
                assert r['own_target_built'] is True
                assert 'Built ' + module in raw.decode() and 'Build completed successfully' in raw.decode()
            else:
                assert '--trust=0' in r['command']
            runs.append({'module': module, 'kind': r['stage'], 'original_stdout': p,
                         'original_stdout_sha256': r['stdout_sha256'], 'source_sha256': r['source_sha256'],
                         'selected_axioms': ax, 'definitions_only_no_prints': not m['selected'],
                         'genuine_own_target_built': r['stage'] == 'normal'})
    selected = [n for m in modules.values() for n in m['selected']]
    assert len(modules) == 10 and len(selected) == len(set(selected)) == 20
    assert len(runs) == 20 and len(failed) == 3
    # Every new module's transitive local import is frozen or one of this exact10.
    allowed = guards | {m['source']: m['source_sha256'] for m in modules.values()}
    pending, closure = [m['source'] for m in modules.values()], set()
    while pending:
        p = pending.pop()
        if p in closure:
            continue
        assert p in allowed and sha(p) == allowed[p], ('unverified dependency', p)
        closure.add(p)
        for name in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$', Path(p).read_text(), re.M):
            pending.append(name.replace('.', '/') + '.lean')
    # Preserve raw-to-existing-public-copy mappings already made by the producers.
    archives = []
    for a in wb['lossless_stdout_archives']:
        raw, pub = a['raw_path'], a['published_gzip']
        assert sha(raw) == a['raw_sha256'] and sha(pub) == a['gzip_sha256']
        assert gzip.decompress(Path(pub).read_bytes()) == Path(raw).read_bytes()
        archives.append({'raw_path': raw, 'raw_sha256': sha(raw), 'published_path': pub,
                         'published_sha256': sha(pub), 'encoding': 'gzip', 'exact_byte_restoration': True})
    for r in obs['runs']:
        raw, pub = r['actual_stdout']['path'], r['published_stdout']['path']
        meta(r['published_stdout'])
        restored = gzip.decompress(Path(pub).read_bytes()) if r['lossless_gzip'] else Path(pub).read_bytes()
        assert restored == Path(raw).read_bytes()
        archives.append({'raw_path': raw, 'raw_sha256': sha(raw), 'published_path': pub,
                         'published_sha256': sha(pub), 'encoding': 'gzip' if r['lossless_gzip'] else 'identity',
                         'exact_byte_restoration': True})
    files.add(PAPER)
    assert all(not p.startswith('.lake/') and not p.endswith(('.olean', '.ilean', '.trace', '.log')) for p in files)
    return base, modules, selected, files, runs, failed, guards, archives


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    base, modules, selected, files, runs, failed, guards, archives = inputs()
    if args.prepare_only:
        projected, projected_archives = archive_projection(files)
        plan = {'status': 'READY_STANDALONE_ONLY_NO_NEW_COMPOSED_GATE', 'modules': modules,
                'new_module_count': 10, 'new_selected_count': 20, 'new_selected': selected,
                'producer_receipt_sha256': FIXED, 'input_file_sha256': {p: sha(p) for p in sorted(files)},
                'immutable_prior_guards': guards, 'finalizer_sha256': sha(HERE),
                'default_gate_unchanged': {'jobs': 10892, 'verified': 2203, 'default_selected': 2196, 'explicit_helpers': 7},
                'root_sha256': base['root_sha256'], 'audit_sha256': base['audit_sha256'],
                'prospective_publication_paths': sorted(projected | {RECEIPT, PUBLISHED_SCRIPT} | set(DOCS)),
                'prospective_lossless_archives': projected_archives,
                'docs_not_read_until_final_run': True, 'weak_scope': 'mask472 only; A75/B225; fixed n4; all delta in [0,1)',
                'research_only': {PAPER: sha(PAPER)}, 'excluded': ['GeneralMaxClump SOURCE_ONLY', 'new four-mask/five-target SOURCE_ONLY', 'all62/all10 or actualF22 closure']}
        Path(PLAN).write_text(json.dumps(plan, indent=2) + '\n')
        print(json.dumps({'status': 'READY', 'plan': PLAN, 'sha256': sha(PLAN), 'input_files': len(files),
                          'modules': 10, 'standalone_selected': 20, 'default_verified_unchanged': 2203}))
        return
    plan = read(PLAN)
    assert plan['finalizer_sha256'] == sha(HERE)
    check_hashes(plan['input_file_sha256'])
    assert plan['modules'] == modules
    projected, projected_archives = archive_projection(files)
    assert projected_archives == plan['prospective_lossless_archives']
    assert sorted(projected | {RECEIPT, PUBLISHED_SCRIPT} | set(DOCS)) == plan['prospective_publication_paths']
    Path(PUBLISHED_SCRIPT).parent.mkdir(parents=True, exist_ok=True)
    if Path(PUBLISHED_SCRIPT).exists():
        assert Path(PUBLISHED_SCRIPT).read_bytes() == Path(HERE).read_bytes()
    else:
        Path(PUBLISHED_SCRIPT).write_bytes(Path(HERE).read_bytes())
    files.add(PUBLISHED_SCRIPT)
    for p in sorted(files):
        q = Path(p)
        if q.suffix not in ['.txt', '.out']:
            continue
        raw = q.read_bytes()
        if 'normal' not in q.name and not any(re.search(rb'[ \t]+$', line) for line in raw.splitlines()):
            continue
        pub = p + '.gz'
        if Path(pub).exists():
            assert gzip.decompress(Path(pub).read_bytes()) == raw
        else:
            Path(pub).write_bytes(gzip.compress(raw, mtime=0))
        archives.append({'raw_path': p, 'raw_sha256': sha(p), 'published_path': pub,
                         'published_sha256': sha(pub), 'encoding': 'gzip', 'exact_byte_restoration': True})
        files.remove(p)
        files.add(pub)
    files.update(DOCS)
    files.add(RECEIPT)
    receipt = {
        'recorded_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status': 'SCOPED_STANDALONE_PASS_LOW4_SUPPORT_AND_MASK472_PILOTS', 'original_problem_complete': False,
        'default_gate_unchanged': plan['default_gate_unchanged'], 'base_default_receipt': {'path': BASE, 'sha256': BASE_SHA},
        'root_sha256': base['root_sha256'], 'audit_sha256': base['audit_sha256'],
        'new_module_count': 10, 'new_selected_count': 20, 'modules': modules, 'new_selected': selected,
        'selected_verification_scope': 'Independent producer strict --trust=0 and genuine own-target Lake builds; no new combined/root audit is claimed.',
        'definitions_only_module': 'Jsp000404.SixWeakOuterReplay', 'definitions_only_axiom_claim': False,
        'producer_receipt_sha256': FIXED, 'successful_checks': runs, 'successful_check_count': 20,
        'weak_pilot_checks': {'total': 17, 'successful': 14, 'failed_NOT_PROVED': 3}, 'failed_attempts': failed,
        'preserved_prior_sha256': guards, 'paper_only_sha256': {**base['paper_only_sha256'], PAPER: sha(PAPER)},
        'lossless_stdout_archives': archives, 'shared_document_sha256': {p: sha(p) for p in DOCS},
        'scope': [
            'WholeBand7: original LOW4 minimum Model internally gives FixedCard17; whole-band maximum/plateau and single-deleted zero-source gap <= 2rho. No two-deletion zero2rho bound.',
            'Observer1: deleting an original score1 target has zero gain at every distinct original positive-score observer. Original zero observers may gain1.',
            'HO1: original generic LOW4 Model excludes an obtuse-heavy center coexisting with another nonacute-heavy center. This is not a whole-F17 exclusion.',
            'Weak7/11: fixed n4, all 0<=delta<1, mask472/catalog26 only. A: row1def<=2,row3def<=3 (75 contexts). B: row0def<=2,row2def<=2 (225 contexts). Other rows arbitrary. No all62/10-pair/actualF22 closure.'
        ],
        'warning_policy': 'All final owned-module warnings are0 in the producer checks; inherited warnings are retained verbatim. WholeBand normal467, Observer normal467, HO normal464; weak per-module raw outputs remain authoritative. No all-output-warning-free claim.',
        'failure_policy': 'Three actual weak API failures and exact source snapshots remain NOT_PROVED, with original raw paths and hashes. No reconstruction or stripping.',
        'historical_ready_note_policy': 'Weak READY.md is historical precheck preparation; final-result.json and RECEIPT.md record the later actual PASS.',
        'not_proved': ['All62 weak pilots or finite all10 pair dispatch', 'ActualF22/fullR2 unconditional capacity', 'Original wholeF17 contradiction or mandatory deletion selector', 'Original arbitrary-N sharp lower theorem/prize completion'],
        'publication_file_whitelist': sorted(files),
        'publication_file_sha256': {p: sha(p) for p in sorted(files) if p != RECEIPT},
    }
    Path(RECEIPT).write_text(json.dumps(receipt, indent=2) + '\n')
    Path(STAGE).write_text(json.dumps(sorted(files), indent=2) + '\n')
    print(json.dumps({'receipt': RECEIPT, 'sha256': sha(RECEIPT), 'files': len(files), 'stage_manifest': STAGE,
                      'new_modules': 10, 'standalone_selected': 20, 'default_verified_unchanged': 2203, 'staged': False}))


if __name__ == '__main__':
    main()
