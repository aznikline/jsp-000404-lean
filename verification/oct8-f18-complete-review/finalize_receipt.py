"""New F18 producer integration; never edits frozen2200 evidence or shared docs.
Prepare reads immutable source/evidence only; final run freezes Root-updated prose.
No Lean/Git execution, no stage/commit.
"""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re
PREP='.lake/oct8-f18-complete-prep.json'
BASE='research/JSP404_WEIGHTED_F18_F17_SUPPORT_INTEGRATION_RECEIPT_20261008.json'
BASE_SHA='ff36333c2667b38840f5b0e34400417c064dafdba9777e131f56fd0e860bed28'
PRODUCER='research/JSP404_ACTUAL_F18_COMPLETE_FINAL_BATCH_RECEIPT_20261008.json'
PRODUCER_SHA='e3aa84fe42a8421ce2276bff07493f7367c7dba283c507d43a5bad42820049ec'
OUT=Path('verification/oct8-f18-complete-review')
RECEIPT='research/JSP404_F18_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def inputs():
    prep=read(PREP);base=read(BASE);producer=read(PRODUCER)
    assert sha(BASE)==BASE_SHA and sha(PRODUCER)==PRODUCER_SHA
    for key in ['preserved_tracked_lean_sha256','source_sha256','paper_only_sha256']:
        for p,h in base[key].items():assert sha(p)==h,p
    # Old logs/scripts/receipt stay frozen; shared Root/Audit/prose intentionally advance.
    for p,h in base['publication_file_sha256'].items():
        if p not in ['Jsp000404.lean','verification/oct5-review/ProofAudit.lean','notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']:assert sha(p)==h,p
    for p,h in producer['publication_file_sha256'].items():assert sha(p)==h,p
    for p,h in prep['new_source_sha256'].items():assert sha(p)==h,p
    assert sha('Jsp000404.lean')==prep['root_after_sha256']
    assert sha('verification/oct5-review/ProofAudit.lean')==prep['audit_after_sha256']
    files=set(producer['publication_file_whitelist']);assert len(files)==32
    allowed=set(base['import_closure_source_sha256'])|set(prep['new_source_sha256'])
    closure=set();pending=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
    while pending:
        p=pending.pop()
        if p in closure:continue
        closure.add(p)
        for m in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$',Path(p).read_text(),re.M):
            q=m.replace('.','/')+'.lean';assert q in allowed,('unverified import',p,q);pending.append(q)
    return prep,base,producer,files,closure

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');args=ap.parse_args()
    prep,base,producer,files,closure=inputs()
    if args.prepare_only:
        p=Path('.lake/oct8-f18-complete-publication-plan.json');p.write_text(json.dumps({'status':'INPUTS_READY_COMPOSED_GATES_NOT_CLAIMED','producer_files':sorted(files),'producer_file_sha256':{q:sha(q) for q in sorted(files)},'new_selected':prep['new_selected'],'requested_verified':2203,'source_guards':prep['new_source_sha256'],'root_sha256':prep['root_after_sha256'],'audit_sha256':prep['audit_after_sha256'],'old2200_frozen_pass':True,'docs_not_read':True},indent=2)+'\n')
        print(json.dumps({'status':'READY','manifest':str(p),'sha256':sha(p),'producer_files':32,'closure_sources':len(closure)}));return
    full=read(OUT/'full.json');audit=read(OUT/'audit.json');gates=read(OUT/'gates.json')
    assert full['exit_code']==audit['exit_code']==0
    for r in [full,audit]:
        assert sha(r['stdout'])==r['stdout_sha256'] and not r['rss_cap_killed'] and not r['timeout_killed']
        assert not r.get('parallel_lean_cap_killed',False)
    assert gates[0]['exit_code']==0 and gates[0]['declaration_count']==2203 and not gates[0]['failures']
    assert gates[1]['exit_code']==1 and gates[1]['failures']==[{'declaration':'Jsp404.sendov_lower','unexpected_axioms':['sorryAx']}]
    for r in gates:assert sha(r['stdout'])==r['stdout_sha256']
    axioms=read(gates[0]['stdout'])['axioms'];assert all(n in axioms and set(axioms[n])<={'propext','Classical.choice','Quot.sound'} for n in prep['new_selected'])
    jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',Path(full['stdout']).read_text()).group(1))
    docs=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
    files.update(docs);files.update(['Jsp000404.lean','verification/oct5-review/ProofAudit.lean'])
    files.update(str(p) for p in OUT.iterdir() if p.is_file() and not p.name.endswith(('.olean','.ilean','.trace')))
    for src,dst in [('.lake/run_oct8_f18_complete_bundle.py',OUT/'run_checks.py'),('.lake/check_oct8_f18_complete_bundle_gates.py',OUT/'check_gates.py'),('.lake/finalize_oct8_f18_complete_bundle.py',OUT/'finalize_receipt.py')]:
        dst.write_bytes(Path(src).read_bytes());files.add(str(dst))
    archives=[]
    for p in sorted(files):
        q=Path(p)
        if q.suffix not in ['.txt','.log','.out']:continue
        raw=q.read_bytes();compress=('normal' in q.name or 'full' in q.name or any(re.search(rb'[ \t]+$',l) for l in raw.splitlines()))
        target=str(q.with_suffix('.stdout.txt')) if q.suffix=='.log' else p
        if compress:
            target+='.gz'
            if Path(target).exists():assert gzip.decompress(Path(target).read_bytes())==raw,target
            else:Path(target).write_bytes(gzip.compress(raw,mtime=0))
        elif target!=p:
            if Path(target).exists():assert Path(target).read_bytes()==raw
            else:Path(target).write_bytes(raw)
        else:continue
        archives.append({'raw_path':p,'raw_sha256':sha(p),'published_path':target,'published_sha256':sha(target),'encoding':'gzip' if compress else 'identity','exact_original_byte_restoration':True})
        files.remove(p);files.add(target)
    assert not any(p.startswith('.lake/') or p.endswith(('.log','.olean','.ilean','.trace')) for p in files)
    files.add(RECEIPT)
    r=dict(recorded_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='SCOPED_PASS_ACTUAL_F18_COMPLETE_MINIMUM_COUNTERMODEL_ORIGINAL_LOWER_OPEN',original_problem_complete=False,
      publication_base_commit='fab739a',base2200_receipt={'path':BASE,'sha256':BASE_SHA},producer_receipt={'path':PRODUCER,'sha256':PRODUCER_SHA},
      new_modules=prep['new_source_sha256'],new_selected=prep['new_selected'],new_selected_count=3,
      composed_standard_axiom_count=2203,default_root_selected_count=2196,existing_explicit_helpers=7,default_build_jobs=jobs,
      full_build=full,composed_trust_zero_audit=audit,standard_axiom_gate=gates[0],original_root_negative_gate=gates[1],
      source_sha256=prep['new_source_sha256'],preserved_old2200_source_sha256=base['source_sha256'],preserved_tracked_lean_sha256=base['preserved_tracked_lean_sha256'],
      old2200_receipt_and_log_hashes={p:h for p,h in base['publication_file_sha256'].items() if p not in ['Jsp000404.lean','verification/oct5-review/ProofAudit.lean','notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']},
      paper_only_sha256=base['paper_only_sha256'],import_closure_source_sha256={p:sha(p) for p in sorted(closure)},root_sha256=sha('Jsp000404.lean'),audit_sha256=sha('verification/oct5-review/ProofAudit.lean'),shared_document_sha256={p:sha(p) for p in docs},lossless_stdout_archives=archives,
      scope='ActualMinimalBandCounterexample.Model o e (pi/(4+1/2)) (pi/4) 16 (s+1) c lam with original potential18 is impossible. Complete internally splits every heavy count; no extra caller heavy-count premise in the final interface.',
      warning_policy='Preserve the one final Complete linter occurrence per successful producer check and all inherited warnings; raw source/output bytes are never stripped. No warning-free claim.',
      failure_policy='The actual d6 initial Complete source/raw are retained NOT_PROVED; only membership API repair, no changed mathematical premises. Old2200 evidence is untouched.',
      not_proved=['Original F17 contradiction or mandatory hull-zero deletion selector','Unconditional actual F22/fullR2 capacity: A/B closures remain explicit hypotheses','Original arbitrary-N sharp lower theorem','Complete prize submission'],
      publication_file_whitelist=sorted(files),publication_file_sha256={p:sha(p) for p in sorted(files) if p!=RECEIPT})
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path('.lake/oct8-f18-complete-stage-files.json').write_text(json.dumps(sorted(files),indent=2)+'\n')
    print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'full_jobs':jobs,'verified':2203,'staged':False}))
if __name__=='__main__':main()
