"""Seal the checked positive-critical profile support only; no Lean/Git/root/audit execution."""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re
OWNER='verification/oct8-high-r1-positive-critical-profile/receipt.json'
BASE='research/JSP404_N4_R2_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
SUPPORT='research/JSP404_HIGH_R1_ENDPOINT_STANDALONE_RECEIPT_20261008.json'
HERE='.lake/finalize_oct8_positive_profile_standalone.py'
PLAN='.lake/oct8-positive-profile-standalone-prep.json'
RECEIPT='research/JSP404_HIGH_R1_POSITIVE_PROFILE_STANDALONE_RECEIPT_20261008.json'
STAGE='.lake/oct8-positive-profile-standalone-stage-files.json'
OUT=Path('verification/oct8-positive-profile-standalone-review')
DOCS=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOTS=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
FIXED={OWNER:'abb7f56c2daf2da924db4208806a6ca52290199cd72f39bf71e4bec2236b4b13',BASE:'dda4a9cff976557911e827f0f461088c4a6b3c7fdb69fbaf8c69f75c87d28187',SUPPORT:'ca6447b3f63510170a105475aa7379269290e14b474af56deaeea7f60b1e95e6'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def hashes(m):
    for p,h in m.items():assert sha(p)==h,('changed frozen file',p)
def inputs():
    hashes(FIXED);owner,base,support=read(OWNER),read(BASE),read(SUPPORT)
    assert owner['status']=='READY' and owner['all_lean_lake_exited_before_formal_return']
    assert sha(owner['source'])==owner['source_sha256']=='c1b25f9a8f17eba30c61768c4637c8a8bfd776ace741c73f4df0a134073cc6d2'
    assert len(owner['selected'])==2 and owner['selected_axioms']==['propext','Classical.choice','Quot.sound']
    assert (base['default_build_jobs'],base['composed_standard_axiom_count'])==(10935,2677)
    assert sha(ROOTS[0])==base['root_sha256'] and sha(ROOTS[1])==base['audit_sha256']
    guards=dict(support['preserved_prior_sha256'])
    for r in [base,support]:guards.update({p:h for p,h in r['publication_file_sha256'].items() if p not in DOCS})
    hashes(guards);hashes(owner['parents_current_sha256'])
    files={OWNER};files.update(f['path'] for f in owner['publication_files'])
    for f in owner['publication_files']:assert sha(f['path'])==f['sha256']
    assert len(files)==14
    success=[];failed=[]
    for r in owner['attempts']:
        assert r['source_unchanged'] and not r['guard_reason']
        assert sha(r['stdout'])==r['stdout_sha256'] and sha(r['snapshot'])==r['snapshot_sha256']==r['source_sha256']
        if r['exit_code']!=0:
            assert r['kind']=='strict0' and r['attempt']==1;failed.append({'status':'NOT_PROVED',**r});continue
        assert r['source_sha256']==owner['source_sha256']
        text=Path(r['stdout']).read_text();ax=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S))
        for n in owner['selected']:assert n in ax and {x.strip() for x in ax[n].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},n
        if r['kind']=='normal':assert r['build_completed_successfully'] and r['own_built_lines'] and 'Built '+owner['module'] in text
        else:assert r['kind']=='strict0' and r['attempt']==2 and '--trust=0' in r['command']
        success.append(r)
    assert len(success)==2 and len(failed)==1
    assert failed[0]['source_sha256'].startswith('6c5e')
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
        p={'status':'READY_STANDALONE_POSITIVE_CRITICAL_PROFILE_ONLY','source':owner['source'],'source_sha256':owner['source_sha256'],'selected':owner['selected'],'input_file_sha256':{p:sha(p) for p in sorted(files)},'producer_receipt_sha256':FIXED,'root_sha256':base['root_sha256'],'audit_sha256':base['audit_sha256'],'default_gate_unchanged':{'jobs':10935,'verified':2677,'default_selected':2670,'explicit_helpers':7},'prior_standalone_support':7,'new_standalone_support':2,'finalizer_sha256':sha(HERE),'docs_not_read':True}
        Path(PLAN).write_text(json.dumps(p,indent=2)+'\n');print(json.dumps({'plan':PLAN,'sha256':sha(PLAN),'producer_files':len(files),'new_selected':2,'default_verified_unchanged':2677}));return
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
    r={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SCOPED_STANDALONE_PASS_ACTUAL_POSITIVE_HIGH_R1_CRITICAL_PROFILE','original_problem_complete':False,'publication_base_commit_reported_by_root':'30aab04f0adaf8bf170b36c9990c2c8cd335aa74','default_gate_unchanged':prep['default_gate_unchanged'],'base2677_receipt':{'path':BASE,'sha256':FIXED[BASE]},'prior_standalone_support_receipt':{'path':SUPPORT,'sha256':FIXED[SUPPORT]},'new_module_count':1,'new_selected_count':2,'new_selected':owner['selected'],'source':owner['source'],'source_sha256':owner['source_sha256'],'producer_receipt':{'path':OWNER,'sha256':FIXED[OWNER]},'successful_checks':success,'failed_NOT_PROVED_attempts':failed,'standalone_support_outside_default':{'previous':7,'this_batch':2,'total':9,'combined_root_audit_claim':False},'root_sha256':base['root_sha256'],'audit_sha256':base['audit_sha256'],'preserved_prior_sha256':guards,'old_paper_only_sha256':base['old_paper_only_sha256'],'new_prior_paper_only_sha256':base['new_paper_only_sha256'],'previous_batch_paper_only_sha256':support['this_batch_paper_only_sha256'],'lossless_stdout_archives':archives,'shared_document_sha256':{p:sha(p) for p in DOCS},'scope':'Original floor4 HIGH minimum-counter Model with cap20, an original SAT, an actual score2 witness and explicit all-original-positive premise: internally derive potential22, seven original points, tail scores1 and the original SATfan heavy endpoint. No caller Phi/cardinality/tail array/zero-gain/chart premise; positivity remains explicit. This is not a contradiction, general positivity or capacity.','warning_policy':'Final source-owned warnings0; normal inherited22169 warning headers preserved verbatim. No warning-free whole-output claim.','failure_policy':'Initial6c5e constructor-parse candidate exact source/raw failed with exit1 and remainsNOT_PROVED; finalc1b25 strict02/normal01 alone count asPASS.','not_proved':['FullHIGH R1 or general capacity','General positivity or arbitrary-n capacity','Original wholeF17 or arbitrary-N lower/prize completion','Weighted7977/RowGainBridge/degreechild WIP'],'publication_file_whitelist':sorted(files),'publication_file_sha256':{p:sha(p) for p in sorted(files) if p!=RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path(STAGE).write_text(json.dumps(sorted(files),indent=2)+'\n');print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'stage_manifest':STAGE,'default_verified_unchanged':2677,'staged':False}))
if __name__=='__main__':main()
