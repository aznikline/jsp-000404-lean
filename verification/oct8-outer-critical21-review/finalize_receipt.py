"""Static input audit; --finalize freezes only this batch receipt and copies.
No Lean, Lake, Git, index, shared source, audit or document mutations.
Shared documents and final run outputs are read only under --finalize.
"""
from pathlib import Path
import argparse, datetime, gzip, hashlib, json, re

PREP = Path('.lake/oct8-outer-critical21-integration-prep.json')
OUT = Path('verification/oct8-outer-critical21-review')
RECEIPT = 'research/JSP404_OUTER_CRITICAL21_INTEGRATION_RECEIPT_20261008.json'
DOCS = ['notes/STATUS.md', 'research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
STD = {'propext', 'Classical.choice', 'Quot.sound'}
IMPORTS = ['N4R2OuterLeftTerminal', 'ActualN4R2CriticalClosure',
           'ActualF18OneHeavyThreeInterior', 'ActualF18OneHeavyFourInterior', 'SixOuterMask000']

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_text())
def check(p, h): assert sha(p) == h, ('hash mismatch', p)
def item_files(item, files):
    check(item['path'], item['sha256']); files.add(item['path'])

def collect():
    prep = read(PREP)
    assert len(prep['preserved_lean_sha256']) == 1928
    assert prep['new_default_imports'] == IMPORTS
    assert len(prep['new_selected']) == len(set(prep['new_selected'])) == 409
    assert prep['verified_requested'] == 2139
    for p, h in prep['preserved_lean_sha256'].items(): check(p, h)
    check('Jsp000404.lean', prep['root_sha256'])
    check('verification/oct5-review/ProofAudit.lean', prep['audit_sha256'])
    check(prep['outer_freeze'], prep['outer_freeze_sha256'])
    outer = read(prep['outer_freeze'])
    assert outer['status'] == 'PASS_ALL24698_WORDS_SCALAR_OUTER_LEFT_PROFILE'
    assert outer['kernel_all_words'] and outer['scalar_outer_left_terminal_ready']
    assert outer['required_module_count'] == 196 and outer['external_soundness_module_count'] == 1
    assert outer['selected_count'] == 397 and len(outer['publish_files']) == 802
    assert outer['file_hashes'] == prep['outer_file_hashes']
    files = set(outer['publish_files']) | {prep['outer_freeze']}
    for p, h in outer['file_hashes'].items(): check(p, h)
    for axes in outer['selected_declarations'].values(): assert set(axes) <= STD
    # F21 receipt names exact existing files; no directory scan or invented evidence.
    f21path = prep['critical21_receipt']; check(f21path, prep['critical21_receipt_sha256'])
    f21 = read(f21path); files.add(f21path)
    assert f21['status'] == 'SCOPED_PASS_ACTUAL_N4_HIGH_CRITICAL21'
    assert f21['module'] == 'Jsp000404.ActualN4R2CriticalClosure'
    assert len(f21['exports']) == 1 and not f21['failed_attempts']
    for key in ['source', 'research_note', 'selected_names', 'historical_source_only_note']:
        item_files(f21[key], files)
    for stage in ['strict0', 'normal']:
        r = f21[stage]
        assert r['exit_code'] == 0 and r['guard']['guard_reason'] is None
        assert r['guard']['source_unchanged'] and r['guard']['source_sha256'] == f21['source']['sha256']
        assert set(r['axioms']) == set(f21['exports'])
        for axes in r['axioms'].values(): assert set(axes) <= STD
        item_files(r['stdout'], files); item_files(r['exact_source_snapshot'], files)
        assert r['exact_source_snapshot']['sha256'] == f21['source']['sha256']
        if stage == 'strict0': assert '--trust=0' in r['command']
        else:
            text = Path(r['stdout']['path']).read_text()
            assert r['own_target_built'] and 'Built Jsp000404.ActualN4R2CriticalClosure' in text
            assert 'Build completed successfully' in text
    # Guard already tracked standalone producers, but do not republish their bundles.
    assert all('Jsp000404/' + m + '.lean' in prep['preserved_lean_sha256'] for m in IMPORTS[2:])
    allowed = set(prep['preserved_lean_sha256']) | {p for p in files if p.endswith('.lean')} | {'Jsp000404.lean'}
    pending = ['Jsp000404.lean', 'verification/oct5-review/ProofAudit.lean']; closure = set()
    while pending:
        p = pending.pop()
        if p in closure: continue
        closure.add(p)
        for m in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$', Path(p).read_text(), re.M):
            q = m.replace('.', '/') + '.lean'
            assert q in allowed, ('unpublished import', p, q)
            pending.append(q)
    return prep, outer, f21, files, closure

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--finalize', action='store_true')
    args = ap.parse_args()
    prep, outer, f21, files, closure = collect()
    if not args.finalize:
        print(json.dumps({'status': 'STATIC_INPUTS_READY_DOCS_NOT_READ',
            'producer_files': len(files), 'new_default_imports': 5, 'new_selected': 409,
            'verified_requested': 2139, 'old_lean_guards': 1928,
            'outer_files_including_freeze': 803, 'f21_files_including_history': 9,
            'import_closure_sources': len(closure)})); return
    assert not Path(RECEIPT).exists(), 'Refusing to replace finalized receipt'
    full, audit, gates = read(OUT / 'full.json'), read(OUT / 'audit.json'), read(OUT / 'gates.json')
    assert full['exit_code'] == audit['exit_code'] == 0
    for r in [full, audit]:
        check(r['stdout'], r['stdout_sha256'])
        assert not r['rss_cap_killed'] and not r['timeout_killed']
    assert full['command'] == ['lake', 'build'] and '--trust=0' in audit['command']
    assert [r['exit_code'] for r in gates] == [0, 1]
    assert gates[0]['declaration_count'] == 2139 and not gates[0]['failures']
    assert gates[1]['failures'] == [{'declaration': 'Jsp404.sendov_lower', 'unexpected_axioms': ['sorryAx']}]
    for r in gates: check(r['stdout'], r['stdout_sha256'])
    verified = read(gates[0]['stdout'])
    assert len(verified['axioms']) == 2139
    assert all(name in verified['axioms'] and set(verified['axioms'][name]) <= STD for name in prep['new_selected'])
    jobs = int(re.search(r'Build completed successfully \((\d+) jobs\)', Path(full['stdout']).read_text()).group(1))
    # The observed job count is authoritative; do not substitute the planning estimate.
    files.update(DOCS); files.update(['Jsp000404.lean', 'verification/oct5-review/ProofAudit.lean'])
    for p in DOCS: assert Path(p).is_file()
    for p in ['full.json', 'full.stdout.txt', 'audit.json', 'audit.stdout.txt',
              'gates.json', 'verified-gate.json', 'root-gate.json']:
        assert (OUT / p).is_file(); files.add(str(OUT / p))
    for src, name in [('.lake/run_oct8_outer_critical21_bundle.py', 'run_checks.py'),
                      ('.lake/check_oct8_outer_critical21_bundle_gates.py', 'check_gates.py'),
                      ('.lake/finalize_oct8_outer_critical21_bundle.py', 'finalize_receipt.py')]:
        dst = str(OUT / name)
        if Path(dst).exists(): assert Path(dst).read_bytes() == Path(src).read_bytes()
        else: Path(dst).write_bytes(Path(src).read_bytes())
        files.add(dst)
    archives = []
    for p in sorted(files):
        if p.endswith('.txt'):
            raw = Path(p).read_bytes()
            if any(re.search(rb'[ \t]+$', line) for line in raw.splitlines()):
                dst = p + '.gz'
                if Path(dst).exists(): assert gzip.decompress(Path(dst).read_bytes()) == raw
                else: Path(dst).write_bytes(gzip.compress(raw, mtime=0))
                archives.append({'raw_path': p, 'raw_sha256': sha(p), 'published_gzip': dst,
                                 'gzip_sha256': sha(dst), 'decompression_restores_exact_raw_bytes': True})
                files.remove(p); files.add(dst)
    assert not any(p.startswith('.lake/') or p.endswith(('.log', '.olean', '.ilean', '.trace')) for p in files)
    assert not any('Weak' in p or 'Weighted' in p or 'SixOuterWordCatalog' in p for p in files)
    files.add(RECEIPT)
    result = dict(recorded_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        status='SCOPED_PASS_OUTER24698_AND_ACTUAL_N4_CRITICAL21_ORIGINAL_LOWER_OPEN',
        original_problem_complete=False, publication_base_commit=prep['base'],
        new_default_imports=prep['new_default_imports'], new_selected=prep['new_selected'],
        new_selected_count=409, composed_standard_axiom_count=2139,
        default_root_selected_count=2132, existing_explicit_helpers=7,
        default_build_jobs=jobs, full_build=full, composed_trust_zero_audit=audit,
        standard_axiom_gate=gates[0], original_root_negative_gate=gates[1],
        outer_freeze=dict(path=prep['outer_freeze'], sha256=prep['outer_freeze_sha256'],
            checked_words=24698, modules=197, selected=397, kernel_all_words=True),
        critical21_producer=dict(path=prep['critical21_receipt'], sha256=prep['critical21_receipt_sha256']),
        preserved_tracked_lean_sha256=prep['preserved_lean_sha256'],
        root_sha256=sha('Jsp000404.lean'), audit_sha256=sha('verification/oct5-review/ProofAudit.lean'),
        shared_document_sha256={p: sha(p) for p in DOCS},
        import_closure_source_sha256={p: sha(p) for p in sorted(closure)},
        lossless_stdout_archives=archives,
        scope=['Complete 24698-word scalar outer-left replay: GenericModel7 4, row1 defect2, rows2..6 defect4, arbitrary row0; no caller word, ID, row certificate or HIGH premise.',
               'Original actual n4 HIGH configuration with at least6 points, distinct scores3,2,2 and exact potential21 is impossible; actual inflation/chart/ranks/tails are produced internally.',
               'Already tracked rigid-four cover2, one-heavy/four-interior1 and fixed-n4 SixOuter prototype19 are newly default imported; SixOuter concrete scope is only mask000 with75 contexts.'],
        warning_policy='Preserve all raw source/output bytes. Outer own lint1532 occurrences (1528 unused-simp in All, 2 each in shards000/192); terminal/core own0. F21 own0 and1942 inherited normal warning lines. No warning-free claim. Trailing stdout, if present, is published losslessly gzipped.',
        source_only_note_policy='Frozen notes named SOURCE_ONLY are preparation history; true compiler receipts and this integration receipt establish current status without rewriting frozen bytes.',
        not_proved=['Actual potential22 and full R2 capacity', 'All62-mask SixOuter replay',
                    'Original arbitrary-N sharp lower theorem', 'Complete prize submission'],
        excluded=['Mutable weak/weighted data and SOURCE_ONLY SixOuter catalog/coverage work',
                  'Private generation input, mutable global checkpoints, build artifacts'],
        publication_file_whitelist=sorted(files),
        publication_file_sha256={p: sha(p) for p in sorted(files) if p != RECEIPT})
    Path(RECEIPT).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'receipt': RECEIPT, 'receipt_sha256': sha(RECEIPT),
                     'files': len(files), 'selected_total': 2139, 'full_build_jobs': jobs, 'staged': False}))

if __name__ == '__main__': main()
