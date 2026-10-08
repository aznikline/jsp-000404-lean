"""Seal the checked endpoint support only; no Lean/Git/root/audit execution."""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re
OWNER='verification/oct8-actual-high-r1-heavy-endpoint/receipt.json'
BASE='research/JSP404_N4_R2_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
SUPPORT='research/JSP404_NEAREST_APEX_STANDALONE_RECEIPT_20261008.json'
PAPER='research/JSP404_GENERAL_N_AB_CYCLE_BALANCE_PAPER_20261008.md'
R01_PAPER='research/JSP404_HIGH4_R01_CRITICAL_FRONTIER_20261008.md'
HERE='.lake/finalize_oct8_endpoint_standalone.py'
PLAN='.lake/oct8-endpoint-standalone-prep.json'
RECEIPT='research/JSP404_HIGH_R1_ENDPOINT_STANDALONE_RECEIPT_20261008.json'
STAGE='.lake/oct8-endpoint-standalone-stage-files.json'
OUT=Path('verification/oct8-endpoint-standalone-review')
DOCS=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOTS=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
FIXED={OWNER:'e5406a2f2e49ac7ad867662cf2f6b51ad9fc7089d229992a00bc57545bcbbcb6',BASE:'dda4a9cff976557911e827f0f461088c4a6b3c7fdb69fbaf8c69f75c87d28187',SUPPORT:'d889ba9c25412ff6bd25d22a81c9031956e722d4b8f864e914918b471e6d4e64',PAPER:'7a182c4fc0e3da4ef5cac80ab61c9d595adc385f3821910869c9bde39d784f6e'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def hashes(m):
    for p,h in m.items():assert sha(p)==h,('changed frozen file',p)
def inputs():
    hashes(FIXED);owner,base,support=read(OWNER),read(BASE),read(SUPPORT)
    assert owner['status']=='READY' and owner['all_lean_lake_exited_before_formal_return']
    assert sha(owner['source'])==owner['source_sha256']=='ae4d9aa67003638117c32ef19ecf294192a714e18d2e501b42086cfed62e6802'
    assert len(owner['selected'])==1 and owner['selected_axioms']==['propext','Classical.choice','Quot.sound']
    assert (base['default_build_jobs'],base['composed_standard_axiom_count'])==(10935,2677)
    assert sha(ROOTS[0])==base['root_sha256'] and sha(ROOTS[1])==base['audit_sha256']
    guards=dict(support['preserved_prior_sha256'])
    for r in [base,support]:guards.update({p:h for p,h in r['publication_file_sha256'].items() if p not in DOCS})
    hashes(guards);hashes(owner['parents_current_sha256'])
    files={OWNER,PAPER};files.update(f['path'] for f in owner['publication_files'])
    for f in owner['publication_files']:assert sha(f['path'])==f['sha256']
    assert len(files)==18
    success=[];failed=[]
    for r in owner['attempts']:
        assert r['source_unchanged'] and not r['guard_reason']
        assert sha(r['stdout'])==r['stdout_sha256'] and sha(r['snapshot'])==r['snapshot_sha256']==r['source_sha256']
        if r['exit_code']!=0:
            assert r['kind']=='strict0' and r['attempt'] in [1,2];failed.append({'status':'NOT_PROVED',**r});continue
        assert r['source_sha256']==owner['source_sha256']
        text=Path(r['stdout']).read_text();ax=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S))
        for n in owner['selected']:assert n in ax and {x.strip() for x in ax[n].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},n
        if r['kind']=='normal':assert r['build_completed_successfully'] and r['own_built_lines'] and 'Built '+owner['module'] in text
        else:assert r['kind']=='strict0' and r['attempt']==3 and '--trust=0' in r['command']
        success.append(r)
    assert len(success)==len(failed)==2
    assert failed[0]['source_sha256'].startswith('10d8') and failed[1]['source_sha256'].startswith('7e80')
    allowed={**guards,owner['source']:owner['source_sha256']};pending=[owner['source']];seen=set()
    while pending:
        p=pending.pop()
        if p in seen:continue
        assert p in allowed and sha(p)==allowed[p],('unverified dependency',p);seen.add(p)
        for m in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$',Path(p).read_text(),re.M):pending.append(m.replace('.','/')+'.lean')
    assert not any('HProfile' in p or 'ZeroDegree' in p or p.startswith('.lake/') for p in files)
    return owner,base,support,files,guards,success,failed
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args();owner,base,support,files,guards,success,failed=inputs()
    if a.prepare_only:
        p={'status':'READY_STANDALONE_ENDPOINT_ONLY','source':owner['source'],'source_sha256':owner['source_sha256'],'selected':owner['selected'],'input_file_sha256':{p:sha(p) for p in sorted(files)},'producer_receipt_sha256':FIXED,'root_sha256':base['root_sha256'],'audit_sha256':base['audit_sha256'],'default_gate_unchanged':{'jobs':10935,'verified':2677,'default_selected':2670,'explicit_helpers':7},'prior_standalone_support':6,'new_standalone_support':1,'finalizer_sha256':sha(HERE),'docs_not_read':True,'paper_only_sha256':{PAPER:sha(PAPER),R01_PAPER:sha(R01_PAPER)}}
        Path(PLAN).write_text(json.dumps(p,indent=2)+'\n');print(json.dumps({'plan':PLAN,'sha256':sha(PLAN),'producer_files':len(files),'new_selected':1,'default_verified_unchanged':2677}));return
    prep=read(PLAN);hashes(prep['input_file_sha256']);assert prep['finalizer_sha256']==sha(HERE)
    OUT.mkdir(parents=True,exist_ok=True);dst=OUT/'finalize_receipt.py'
    if dst.exists():assert dst.read_bytes()==Path(HERE).read_bytes()
    else:dst.write_bytes(Path(HERE).read_bytes())
    files.add(str(dst));archives=[]
    for p in sorted(files):
        if Path(p).suffix not in ['.txt','.out']:continue
        raw=Path(p).read_bytes()
        if 'normal' not in Path(p).name and not any(re.search(rb'[ \t]+$',line) for line in raw.splitlines()):continue
        pub=p+'.gz'
        if Path(pub).exists():assert gzip.decompress(Path(pub).read_bytes())==raw
        else:Path(pub).write_bytes(gzip.compress(raw,mtime=0))
        archives.append({'raw_path':p,'raw_sha256':sha(p),'published_path':pub,'published_sha256':sha(pub),'encoding':'gzip','exact_original_byte_restoration':True});files.remove(p);files.add(pub)
    files.update(DOCS);files.add(RECEIPT)
    r={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SCOPED_STANDALONE_PASS_ACTUAL_FIN7_HEAVY_ENDPOINT','original_problem_complete':False,'publication_base_commit_reported_by_root':'cf5cf066ee03a362ae4a0a53d3faaa100826e788','default_gate_unchanged':prep['default_gate_unchanged'],'base2677_receipt':{'path':BASE,'sha256':FIXED[BASE]},'prior_standalone_support_receipt':{'path':SUPPORT,'sha256':FIXED[SUPPORT]},'new_module_count':1,'new_selected_count':1,'new_selected':owner['selected'],'source':owner['source'],'source_sha256':owner['source_sha256'],'producer_receipt':{'path':OWNER,'sha256':FIXED[OWNER]},'successful_checks':success,'failed_NOT_PROVED_attempts':failed,'standalone_support_outside_default':{'previous':6,'this_batch':1,'total':7,'combined_root_audit_claim':False},'root_sha256':base['root_sha256'],'audit_sha256':base['audit_sha256'],'preserved_prior_sha256':guards,'old_paper_only_sha256':base['old_paper_only_sha256'],'new_prior_paper_only_sha256':base['new_paper_only_sha256'],'this_batch_paper_only_sha256':prep['paper_only_sha256'],'lossless_stdout_archives':archives,'shared_document_sha256':{p:sha(p) for p in DOCS},'scope':'Original actual Fin7 legal configuration at floor4 HIGH with distinct SAT and score2 centers and everyother original row score1: internally produce SAT fan/reference/sorted indices and prove heavy is first orlast endpoint. No caller chart/rank/word/Phi witness. This is an endpoint producer, not a contradiction or fullR1 capacity.','warning_policy':'Final source-owned warnings0; normal inherited425 warning headers preserved verbatim. No warning-free whole-output claim.','failure_policy':'Initial10d8 and second7e80 exact source/raw failed with exit1 and remainNOT_PROVED; finalae4d strict03/normal01 alone count asPASS.','not_proved':['FullHIGH R1 or general capacity','General-n A/B derivation bridge; paper is zeroKernel and no n5SAT claim','Original wholeF17 or arbitrary-N lower/prize completion','New H-profile SourceOnly/unknown zeroDegree drafts'],'publication_file_whitelist':sorted(files),'publication_file_sha256':{p:sha(p) for p in sorted(files) if p!=RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path(STAGE).write_text(json.dumps(sorted(files),indent=2)+'\n');print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'stage_manifest':STAGE,'default_verified_unchanged':2677,'staged':False}))
if __name__=='__main__':main()
