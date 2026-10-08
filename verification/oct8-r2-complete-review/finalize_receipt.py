"""Seal measured R2 checks and exact producer evidence. No Lean/Git execution."""
from pathlib import Path
import argparse, datetime, gzip, hashlib, json, re
PREP='.lake/oct8-r2-complete-draft.json'
PLAN='.lake/oct8-r2-complete-publication-plan.json'
RECEIPT='research/JSP404_N4_R2_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
STAGE='.lake/oct8-r2-complete-stage-files.json'
BASE='research/JSP404_UNIFORM_FOURMASK_INTEGRATION_RECEIPT_20261008.json'
STAND='research/JSP404_G01_GENERAL_STANDALONE_RECEIPT_20261008.json'
OUT=Path('verification/oct8-r2-complete-review')
FINAL=Path('verification/oct8-six-weak-all-complete')
DOCS=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOTS=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
STD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def hashes(m):
    for p,h in m.items():assert sha(p)==h,('changed frozen file',p)
def inputs():
    prep,base,stand=read(PREP),read(BASE),read(STAND)
    assert prep['status']=='READY_PRODUCERS_ROOT_AUTHORIZED' and not prep['pending_modules']
    assert sha(ROOTS[0])==prep['root_after_sha256'] and sha(ROOTS[1])==prep['audit_after_sha256']
    hashes(prep['new_source_sha256']);hashes(prep['optional_paper_candidates_sha256'])
    guards={}
    for k in ['preserved_prior_sha256','source_sha256','import_closure_source_sha256','paper_only_sha256']:guards.update(base[k])
    for r in [base,stand]:guards.update({p:h for p,h in r['publication_file_sha256'].items() if p not in ROOTS+DOCS})
    guards={p:h for p,h in guards.items() if p not in ROOTS+DOCS};hashes(guards)
    groups=read('.lake/oct8-r2-groups234-evidence-allowlist.json');hashes(groups['input_file_sha256'])
    files=set(groups['input_file_sha256'])|set(stand['publication_file_whitelist'])-set(DOCS)
    final=read(FINAL/'final-result.json');allow=read(FINAL/'allowlist.json')
    assert sha(FINAL/'RECEIPT.md')=='79a9e41a8de66d8a0c06457a25e5be799cad2b5212aeb73d4137b6ef4217556b'
    assert sha(FINAL/'final-result.json')=='b9941a62e4eabd565c89fe82aca996e81789ed28d6f93ae8745de0b6a1b7f1b4'
    assert sha(FINAL/'allowlist.json')=='3e581affbb7b070cda1dbde3258817e88eb68580ab27667eb87b28ea43e26e98'
    assert allow['selected_count']==5
    for name in ['RECEIPT.md','final-result.json','allowlist.json','module-allowlist.txt','compile-plan.json','check.py','compile-plan.initial-three-targets.json','check.initial-three-targets.py','source-ready.json','final-four-targets-ready.json','ActualN4R2Capacity.initial.source.lean']:files.add(str(FINAL/name))
    for m in allow['modules']:
        assert sha(m['source'])==m['sha256']==prep['new_source_sha256'][m['source']]
        files.add(m['source']);cp=FINAL/m['module'].split('.')[-1]/'checkpoint.json';files.add(str(cp))
        rs=read(cp)['attempts'];assert len(rs)==2
        for r in rs:
            assert r['status']=='PASS' and r['exit_code']==0 and not r['resource_stop']
            assert sha(r['stdout'])==r['stdout_sha256'] and sha(r['source_snapshot'])==r['source_snapshot_sha256']==m['sha256']
            if r['stage']=='normal':assert r['own_target_built']
            files.update([r['stdout'],r['source_snapshot']])
    files.update(prep['new_source_sha256']);files.update(prep['optional_paper_candidates_sha256'])
    assert len(prep['modules'])==26 and len(set(prep['new_selected']))==421
    assert not any('LowApex' in p or 'Nearest.source' in p or '/corpus/' in p for p in files)
    return prep,base,stand,files,guards
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args()
    prep,base,stand,files,guards=inputs()
    if a.prepare_only:
        r={'status':'READY_PRODUCERS_COMPOSED_CHECKS_REQUIRE_ACTUAL_GATE','producer_files':sorted(files),'producer_file_sha256':{p:sha(p) for p in sorted(files)},'new_modules':26,'new_selected':421,'verified_requested':2677,'default_requested':2670,'root_sha256':prep['root_after_sha256'],'audit_sha256':prep['audit_after_sha256'],'paper_candidates':prep['optional_paper_candidates_sha256'],'docs_not_read':True}
        Path(PLAN).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'plan':PLAN,'sha256':sha(PLAN),'producer_files':len(files)}));return
    plan=read(PLAN);hashes(plan['producer_file_sha256'])
    full,audit,gates=read(OUT/'full.json'),read(OUT/'audit.json'),read(OUT/'gates.json')
    for r in [full,audit]:
        assert r['exit_code']==0 and not r['rss_cap_killed'] and not r['timeout_killed'] and not r['parallel_lean_cap_killed'] and r['max_global_lean_count']<=1
        assert sha(r['stdout'])==r['stdout_sha256']
    assert gates[0]['exit_code']==0 and gates[0]['declaration_count']==2677 and not gates[0]['failures']
    assert gates[1]['exit_code']==1 and gates[1]['failures']==[{'declaration':'Jsp404.sendov_lower','unexpected_axioms':['sorryAx']}]
    for r in gates:assert sha(r['stdout'])==r['stdout_sha256']
    ax=read(gates[0]['stdout'])['axioms'];assert all(n in ax and set(ax[n])<=STD for n in prep['new_selected'])
    jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',Path(full['stdout']).read_text()).group(1))
    files.update(DOCS+ROOTS)
    files.update(str(OUT/p) for p in ['root-before.lean','audit-before.lean','full.json','full.stdout.txt','audit.json','audit.stdout.txt','gates.json','verified-gate.json','root-gate.json'])
    for src,name in [('.lake/run_oct8_r2_complete_bundle_draft.py','run_checks.py'),('.lake/check_oct8_r2_complete_bundle_gates_draft.py','check_gates.py'),('.lake/finalize_oct8_r2_complete_bundle.py','finalize_receipt.py')]:
        dst=OUT/name
        if dst.exists():assert dst.read_bytes()==Path(src).read_bytes()
        else:dst.write_bytes(Path(src).read_bytes())
        files.add(str(dst))
    archives=list(stand['lossless_stdout_archives'])
    for p in sorted(files):
        if Path(p).suffix not in ['.txt','.out']:continue
        raw=Path(p).read_bytes()
        if 'normal' not in Path(p).name and 'full' not in Path(p).name and not any(re.search(rb'[ \t]+$',line) for line in raw.splitlines()):continue
        pub=p+'.gz'
        if Path(pub).exists():assert gzip.decompress(Path(pub).read_bytes())==raw
        else:Path(pub).write_bytes(gzip.compress(raw,mtime=0))
        archives.append({'raw_path':p,'raw_sha256':sha(p),'published_path':pub,'published_sha256':sha(pub),'encoding':'gzip','exact_original_byte_restoration':True});files.remove(p);files.add(pub)
    files.add(RECEIPT)
    r={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SCOPED_PASS_COMPLETE_N4_HIGH_R2_ORIGINAL_LOWER_OPEN','original_problem_complete':False,'publication_base_commit_reported_by_root':prep['publication_base_commit_reported_by_root'],'base2256_receipt':{'path':BASE,'sha256':sha(BASE)},'prior_standalone_receipt':{'path':STAND,'sha256':sha(STAND)},'final_four_receipt':{'path':str(FINAL/'RECEIPT.md'),'sha256':sha(FINAL/'RECEIPT.md')},'new_modules':prep['modules'],'new_module_count':26,'new_selected':prep['new_selected'],'new_selected_count':421,'composed_standard_axiom_count':2677,'default_root_selected_count':2670,'existing_explicit_helpers':7,'default_build_jobs':jobs,'full_build':full,'composed_trust_zero_audit':audit,'standard_axiom_gate':gates[0],'original_root_negative_gate':gates[1],'source_sha256':prep['new_source_sha256'],'normal_reuse_records':prep['normal_reuse_records'],'preserved_prior_sha256':guards,'import_closure_source_sha256':prep['candidate_import_closure_source_sha256'],'old_paper_only_sha256':base['paper_only_sha256'],'new_paper_only_sha256':prep['optional_paper_candidates_sha256'],'root_sha256':sha(ROOTS[0]),'audit_sha256':sha(ROOTS[1]),'shared_document_sha256':{p:sha(p) for p in DOCS},'lossless_stdout_archives':archives,'scope':['All62 catalog words are covered internally, yielding unconditional scalar weakA/B contradictions for GenericModel5 at fixedn4 and its full delta[0,1).','Actual floor4 HIGH delta>=1/2 original legal configurations, with an original SAT and two distinct originaldefect2 centers, have potential<=20 at every point count. No caller weak closure, word, row-order, accepted-cycle, Phi or pointcount cap premise remains.','GeneralHO and UniqueZeroClass retain their precise originalLOW Model and geometric/unique-zero premises; UniqueZeroClass supplies classweights, not a wholeF17 contradiction.','Two approved primary-source audit/closed-endpoint erratum files are PAPER only, adding zero kernel declarations.'],'warning_policy':'Final producer-owned warnings0; all inherited/composed warning output preserved byte-for-byte. No all-output-warning-free claim.','failure_policy':'G02/03/G04 and final4 had zero failures. GeneralHO0a294 and UniqueZero1f04 exact failed source/raw remain NOT_PROVED in the included prior standalone evidence; all earlier public source/log/receipt hashes are frozen.','not_proved':['Original F17 contradiction or mandatory deletion selector','Arbitrary-n HIGH R2/general capacity','Original arbitrary-N sharp lower theorem/prize completion','New LowApex/nearest SOURCE_ONLY work'],'publication_file_whitelist':sorted(files),'publication_file_sha256':{p:sha(p) for p in sorted(files) if p!=RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path(STAGE).write_text(json.dumps(sorted(files),indent=2)+'\n');print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'stage_manifest':STAGE,'verified':2677,'full_jobs':jobs,'staged':False}))
if __name__=='__main__':main()
