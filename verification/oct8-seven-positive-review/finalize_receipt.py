"""Seal actual positive HIGH4 integration and honest resource history. No Lean/Git."""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re
PREP='.lake/oct8-seven-positive-integration-prep.json'
PLAN='.lake/oct8-seven-positive-publication-plan.json'
RECEIPT='research/JSP404_ACTUAL_HIGH_POSITIVE_CAPACITY_INTEGRATION_RECEIPT_20261008.json'
STAGE='.lake/oct8-seven-positive-stage-files.json'
BASE='research/JSP404_ACTUAL_SUPPORT18_INTEGRATION_RECEIPT_20261008.json'
OUT=Path('verification/oct8-seven-positive-review')
DOCS=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOTS=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
OWNERS=['research/JSP404_SEVEN_LOWER_REPLAY_CORE_RECEIPT_20261008.json','research/JSP404_SEVEN_LOWER_CHECK_COMPOSE_RECEIPT_20261008.json','research/JSP404_SEVEN_WEAK_FLOOR_PROFILES_RECEIPT_20261008.json']
ADAPTER='verification/oct8-high-r1-seven-lower-adapter/receipt.json'
PHASES=['oct8-seven-lower-data-local','oct8-seven-lower-fixed-cut-pilot-local','oct8-seven-lower-fixed-cut-rest-root','oct8-seven-lower-small-piece-pilot-root','oct8-seven-lower-small-pieces-rest-root','oct8-seven-final-three-root']
META_FOLDERS=['oct8-seven-lower-lean-data-source','oct8-seven-lower-fixed-cut-source','oct8-seven-lower-small-pieces-source','oct8-seven-lower-complete-source-history']
STD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def hashes(m):
    for p,h in m.items():assert sha(p)==h,('changed frozen file',p)
def inputs():
    prep,base=read(PREP),read(BASE);hashes(prep['new_source_sha256'])
    assert sha(ROOTS[0])==prep['root_after_sha256'] and sha(ROOTS[1])==prep['audit_after_sha256']
    guards={}
    for k in ['preserved_prior_sha256','source_sha256','import_closure_source_sha256','paper_only_sha256']:guards.update(base[k])
    guards.update({p:h for p,h in base['publication_file_sha256'].items() if p not in ROOTS+DOCS})
    guards={p:h for p,h in guards.items() if p not in ROOTS+DOCS};hashes(guards)
    files=set(prep['new_source_sha256']);receipts={};history=[]
    for p in OWNERS:
        r=read(p);receipts[p]=sha(p);files.add(p)
        files.update(f['path'] for f in r['publish_files'])
        for f in r['publish_files']:assert sha(f['path'])==f['sha256']
    a=read(ADAPTER);assert not a['publication_authorized'] and not a['terminal_parameter_discharged']
    receipts[ADAPTER]=sha(ADAPTER);files.add(ADAPTER)
    for f in a['held_review_allowlist']:assert sha(f['path'])==f['sha256'];files.add(f['path'])
    for phase in PHASES:
        folder=Path('verification')/phase
        for name in ['compile-plan.json','compile-plan.initial.json','compile-plan.initial-byte-identical-reconstruction.json','check.py','check.initial.py','api-repair01.json','partial-receipt.json','initial-source.lean','run_continuous.py','run_resume.py']:
            p=folder/name
            if p.is_file():files.add(str(p))
        for cp in folder.glob('*/checkpoint.json'):
            files.add(str(cp));record=read(cp)
            for r in record['attempts']:
                assert sha(r['stdout'])==r['stdout_sha256'] and sha(r['source_snapshot'])==r['source_snapshot_sha256']==r['source_sha256']
                files.update([r['stdout'],r['source_snapshot']])
                stop=r.get('resource_stop')
                if stop:category='RESOURCE_'+stop+'_NOT_ACCEPTED'
                elif r['stage']=='normal' and r['exit_code']==0 and r.get('own_target_built') is False:category='CACHED_NORMAL_NON_NEW_EVIDENCE'
                elif r['status']=='PASS' and r['exit_code']==0:category='PASS_RECORD_REQUIRES_CURRENT_SOURCE_MATCH'
                else:category='COMPILER_OR_PROOF_FAILURE_NOT_PROVED'
                history.append({'checkpoint':str(cp),'module':record['module'],'category':category,'record':r})
    for folder in META_FOLDERS:
        p=Path('verification')/folder
        for q in p.iterdir():
            if q.is_file() and q.suffix in ['.json','.txt','.md','.py','.lean']:files.add(str(q))
    # The pilot is independent auxiliary evidence; the failed full-root Jsp source is excluded.
    pilot='Jsp000404/SevenLowerBranchPilot.lean';files.add(pilot)
    assert 'Jsp000404/SevenLowerBranchRootCheck.lean' not in files
    assert not any(p.startswith('.lake/') or p.endswith(('.olean','.ilean','.trace')) for p in files)
    assert not any('/data/branch-dag' in p or '/scalar' in p.lower() for p in files)
    for family in ['strict_reuse_records','normal_reuse_records']:
        for module,r in prep[family].items():
            assert sha(r['stdout'])==r['stdout_sha256'] and sha(r['source_snapshot'])==r['source_snapshot_sha256']==r['source_sha256']
    return prep,base,files,guards,receipts,history
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args();prep,base,files,guards,receipts,history=inputs()
    if a.prepare_only:
        r={'status':'READY_ACCEPTED_DEPENDENCIES_AND_MEASURED_GATES_REQUIRED','producer_files':sorted(files),'producer_file_sha256':{p:sha(p) for p in sorted(files)},'active_sources':prep['new_source_count'],'active_selected':prep['new_selected_count'],'requested_verified':prep['requested_verified'],'root_sha256':prep['root_after_sha256'],'audit_sha256':prep['audit_after_sha256'],'docs_not_read':True,'auxiliary_pilot_selected':1,'auxiliary_pilot_in_default':False}
        Path(PLAN).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'plan':PLAN,'sha256':sha(PLAN),'producer_files':len(files)}));return
    plan=read(PLAN);hashes(plan['producer_file_sha256'])
    full,audit,gates=read(OUT/'full.json'),read(OUT/'audit.json'),read(OUT/'gates.json')
    for r in [full,audit]:
        assert r['exit_code']==0 and not r['rss_cap_killed'] and not r['timeout_killed'] and not r['parallel_lean_cap_killed'] and r['max_global_lean_count']<=1
        assert sha(r['stdout'])==r['stdout_sha256']
    count=prep['requested_verified'];assert gates[0]['exit_code']==0 and gates[0]['declaration_count']==count and not gates[0]['failures']
    assert gates[1]['exit_code']==1 and gates[1]['failures']==[{'declaration':'Jsp404.sendov_lower','unexpected_axioms':['sorryAx']}]
    for r in gates:assert sha(r['stdout'])==r['stdout_sha256']
    ax=read(gates[0]['stdout'])['axioms'];assert all(n in ax and set(ax[n])<=STD for n in prep['new_selected'])
    jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',Path(full['stdout']).read_text()).group(1))
    files.update(ROOTS+DOCS);files.update(str(OUT/p) for p in ['root-before.lean','audit-before.lean','full.json','full.stdout.txt','audit.json','audit.stdout.txt','gates.json','verified-gate.json','root-gate.json'])
    for src,name in [('.lake/run_oct8_seven_positive_integration.py','run_checks.py'),('.lake/check_oct8_seven_positive_integration_gates.py','check_gates.py'),('.lake/finalize_oct8_seven_positive_integration.py','finalize_receipt.py')]:
        p=OUT/name
        if p.exists():assert p.read_bytes()==Path(src).read_bytes()
        else:p.write_bytes(Path(src).read_bytes())
        files.add(str(p))
    archives=[]
    for p in sorted(files):
        if Path(p).suffix not in ['.txt','.out']:continue
        raw=Path(p).read_bytes()
        if 'normal' not in Path(p).name and 'full' not in Path(p).name and not any(re.search(rb'[ \t]+$',line) for line in raw.splitlines()):continue
        dest=p+'.gz'
        if Path(dest).exists():assert gzip.decompress(Path(dest).read_bytes())==raw
        else:Path(dest).write_bytes(gzip.compress(raw,mtime=0))
        archives.append({'raw_path':p,'raw_sha256':sha(p),'published_path':dest,'published_sha256':sha(dest),'encoding':'gzip','exact_original_byte_restoration':True});files.remove(p);files.add(dest)
    files.add(RECEIPT);classes={}
    for r in history:classes[r['category']]=classes.get(r['category'],0)+1
    r={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SCOPED_PASS_ACTUAL_POSITIVE_HIGH4_SAT_HEAVY_CAPACITY','original_problem_complete':False,'publication_base_commit':'9090f6a7c0f7f1a2c4cdbddfac0b6c9cf406e474','base2695_receipt':{'path':BASE,'sha256':sha(BASE)},'producer_receipt_sha256':receipts,'new_active_module_count':prep['new_source_count'],'new_selected_count':prep['new_selected_count'],'modules':prep['modules'],'new_selected':prep['new_selected'],'composed_standard_axiom_count':count,'default_root_selected_count':count-7,'existing_explicit_helpers':7,'default_build_jobs':jobs,'full_build':full,'composed_trust_zero_audit':audit,'standard_axiom_gate':gates[0],'original_root_negative_gate':gates[1],'source_sha256':prep['new_source_sha256'],'normal_reuse_records':prep['normal_reuse_records'],'strict_reuse_records':prep['strict_reuse_records'],'preserved_prior_sha256':guards,'import_closure_source_sha256':prep['actual_import_closure_source_sha256'],'paper_only_sha256':base['paper_only_sha256'],'root_sha256':sha(ROOTS[0]),'audit_sha256':sha(ROOTS[1]),'shared_document_sha256':{p:sha(p) for p in DOCS},'lossless_stdout_archives':archives,'auxiliary_pilot':{'source':'Jsp000404/SevenLowerBranchPilot.lean','selected':['Jsp404.SevenLowerBranchPilot.first_cycle_checked'],'independent_two_stage_PASS':True,'included_in_default_or_composed_count':False},'held_adapter_resolution':'Historical heldreceipt remains immutable. Root explicitly authorized joint integration after true scalarprovider and actualClosure filled the terminal internally. Conditional Adapter2 is counted only as its real conditional statements, not as an unproved unconditional provider.','scope':['Actual original legal configurations at floor4 HIGH with originalSAT, a distinct heavy with kappa>=2 and explicit allpositive, at arbitrary pointcount t: t<=6 and potential<=20. No minimumModel, callerterminal/7subset/profile/phi/cardcap premise.','Typed GenericModel6 lower-only provider has row0def<=2 and rows1/2/3/5def<=3, withrow4free; noHIGH or gauge assumption. RootBoolean goal is exactly check(nodes,cycles,26,empty,10813)=true.','Actual seven-point original profile(3,2,1^5) and the original positive HIGH cap20 minimumModel branch are impossible without callerterminal. Positivity remains explicit.','Zero-score R1 branch, R0, generaln and original arbitrary-N lower/prize completion remainOPEN.'],'resource_and_failure_history':history,'attempt_category_counts':classes,'failure_policy':'CoarseRoot41fc and originalbigGroup01718fb TIME_CAP180 remainNOT_ACCEPTED, not mathematical counterexamples. Part00/Part13.02/Part13.03 MULTIPLE_LEAN stops remain concurrency refusals distinct from later genuinePASS. Ctx cachednormal2 is non-new evidence; currentSHA acceptednormal1 remainsvalid. be05 semantic and initialShard00 errors remain real compiler failures.','initial_metadata_policy':'Providerdf32 is a savedNOT_COMPILED initial wrapper, not a compilerfailure. Byte-identical reconstructedinitialcompileplan is control metadata only; no failed source/raw or compiler run was reconstructed. All source-only/generation labels remain historical bytes.','warning_policy':'Semanticcore has1ownedstylewarning in each successfulstage (normal138prefix=1own+137inherited); Composer0. All inherited/rawwarnings retained, no all-warning-free claim.','not_proof_evidence':['DiagnosticUNSAT','Sourceclosed or partialDAG','Generation manifests without true kernel checks'],'publication_file_whitelist':sorted(files),'publication_file_sha256':{p:sha(p) for p in sorted(files) if p!=RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path(STAGE).write_text(json.dumps(sorted(files),indent=2)+'\n');print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'stage_manifest':STAGE,'full_jobs':jobs,'verified':count,'staged':False}))
if __name__=='__main__':main()
