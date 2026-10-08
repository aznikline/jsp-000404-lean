"""Seal checked HIGH interior class-weight support; no Lean/Git/root edits."""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re
OWNER='research/JSP404_ACTUAL_HIGH_R1_INTERIOR_CLASS_WEIGHT_RECEIPT_20261008.json'
BASE='research/JSP404_N4_R2_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
PRIOR='research/JSP404_EMISSION_BUDGET_STANDALONE_RECEIPT_20261008.json'
HERE='.lake/finalize_oct8_class_weight_standalone.py'
PLAN='.lake/oct8-class-weight-standalone-prep.json'
RECEIPT='research/JSP404_HIGH_R1_CLASS_WEIGHT_STANDALONE_RECEIPT_20261008.json'
STAGE='.lake/oct8-class-weight-standalone-stage-files.json'
OUT=Path('verification/oct8-class-weight-standalone-review')
DOCS=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOTS=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
FIXED={OWNER:'216436369c347f1f7e0b216864526c8f742689e2c9a9a6fb89aae168dd35d3d8',BASE:'dda4a9cff976557911e827f0f461088c4a6b3c7fdb69fbaf8c69f75c87d28187',PRIOR:'f59422f8064a60f062f2ac8f58dd9139bed4768445ebd856977ab65b3230d21b'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def hashes(m):
    for p,h in m.items():assert sha(p)==h,('changed frozen file',p)
def meta(m):assert sha(m['path'])==m['sha256'],m['path']
def inputs():
    hashes(FIXED);owner,base,prior=read(OWNER),read(BASE),read(PRIOR)
    assert owner['all_selected_exact_Std3_both_stages'] and owner['all_dispatched_processes_exited']
    assert owner['selected_count']==1 and owner['failed_attempt_count']==1
    meta(owner['source']);hashes(owner['protected_true_parent_sources'])
    assert owner['source']['sha256']=='b760f190b9aece60010bdbca4d0cc49a51cdd49efbf99300c3ab5066172e31bf'
    assert (base['default_build_jobs'],base['composed_standard_axiom_count'])==(10935,2677)
    assert sha(ROOTS[0])==base['root_sha256'] and sha(ROOTS[1])==base['audit_sha256']
    guards=dict(prior['preserved_prior_sha256'])
    for r in [base,prior]:guards.update({p:h for p,h in r['publication_file_sha256'].items() if p not in DOCS})
    hashes(guards);files={OWNER}
    for f in owner['publish_files']:meta(f);files.add(f['path'])
    assert len(files)==15
    success=[]
    for kind in ['strict0','normal']:
        r=owner[kind];assert r['status']=='PASS' and r['exit_code']==0 and not r['resource_stop']
        assert sha(r['source_snapshot'])==r['source_snapshot_sha256']==r['source_sha256_after']==owner['source']['sha256']
        assert sha(r['log'])==r['log_sha256'];hashes(r['protected_true_parent_sources_after'])
        text=Path(r['log']).read_text();ax=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S))
        for n in owner['selected_declarations']:assert n in ax and {x.strip() for x in ax[n].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},n
        if kind=='normal':assert r['own_target_built'] and 'Built '+owner['module'] in text and 'Build completed successfully' in text
        else:assert '--trust=0' in r['command']
        success.append(r)
    failed=read(owner['failed_attempt_receipt']['path']);meta(owner['failed_attempt_receipt'])
    assert failed['status']=='NOT_PROVED' and failed['source_sha256'].startswith('7977') and len(failed['results'])==1
    f=failed['results'][0];assert f['exit_code']!=0 and f['status']=='NOT_PROVED' and not f['resource_stop']
    assert sha(f['source_snapshot'])==f['source_snapshot_sha256']==failed['source_sha256'] and sha(f['log'])==f['log_sha256']
    archives=[]
    for a in owner['lossless_log_copies']:
        meta(a['raw']);meta(a['lossless_gzip']);assert gzip.decompress(Path(a['lossless_gzip']['path']).read_bytes())==Path(a['raw']['path']).read_bytes()
        archives.append({'raw_path':a['raw']['path'],'raw_sha256':a['raw']['sha256'],'published_path':a['lossless_gzip']['path'],'published_sha256':a['lossless_gzip']['sha256'],'encoding':'gzip','exact_original_byte_restoration':True})
    allowed={**guards,owner['source']['path']:owner['source']['sha256']};queue=[owner['source']['path']];seen=set()
    while queue:
        p=queue.pop()
        if p in seen:continue
        assert p in allowed and sha(p)==allowed[p],('unverified dependency',p);seen.add(p)
        for n in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$',Path(p).read_text(),re.M):queue.append(n.replace('.','/')+'.lean')
    assert not any('Apex' in p or 'LowLB' in p for p in files)
    return owner,base,prior,files,guards,success,failed,archives
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args();owner,base,prior,files,guards,success,failed,archives=inputs()
    if a.prepare_only:
        r={'status':'READY_CLASS_WEIGHT_STANDALONE_ONLY','input_file_sha256':{p:sha(p) for p in sorted(files)},'producer_receipt_sha256':FIXED,'finalizer_sha256':sha(HERE),'new_selected_count':1,'standalone_previous':11,'standalone_total':12,'default_verified_unchanged':2677,'docs_not_read':True}
        Path(PLAN).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'plan':PLAN,'sha256':sha(PLAN),'producer_files':len(files),'selected':1}));return
    prep=read(PLAN);hashes(prep['input_file_sha256']);assert prep['finalizer_sha256']==sha(HERE)
    OUT.mkdir(parents=True,exist_ok=True);dst=OUT/'finalize_receipt.py'
    if dst.exists():assert dst.read_bytes()==Path(HERE).read_bytes()
    else:dst.write_bytes(Path(HERE).read_bytes())
    files.add(str(dst));files.update(DOCS);files.add(RECEIPT)
    paper=owner['historical_PAPER_note'];meta(paper)
    r={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SCOPED_STANDALONE_PASS_ORIGINAL_HIGH_R1_INTERIOR_CLASS_WEIGHT','original_problem_complete':False,'publication_base_commit_reported_by_root':'535693395fb329746a219cbe9745ce88c06d82f9','default_gate_unchanged':{'jobs':10935,'verified':2677,'default_selected':2670,'explicit_helpers':7},'base2677_receipt':{'path':BASE,'sha256':FIXED[BASE]},'prior_standalone_receipt':{'path':PRIOR,'sha256':FIXED[PRIOR]},'producer_receipt':{'path':OWNER,'sha256':FIXED[OWNER]},'new_module_count':1,'new_selected_count':1,'new_selected':owner['selected_declarations'],'source':owner['source'],'successful_checks':success,'failed_NOT_PROVED_attempt':failed,'standalone_support_outside_default':{'previous':11,'this_batch':1,'total':12,'combined_root_audit_claim':False},'root_sha256':base['root_sha256'],'audit_sha256':base['audit_sha256'],'preserved_prior_sha256':guards,'this_batch_paper_only_sha256':{paper['path']:paper['sha256']},'lossless_stdout_archives':archives,'shared_document_sha256':{p:sha(p) for p in DOCS},'scope':owner['scope'],'scope_limit':owner['scope_limit'],'warning_policy':'Final owned warnings0; all22224 inherited normal warning headers and10 trailing-whitespace lines retained in exact-byte-restoring gzip. No whole-output-warning-free claim.','failure_policy':'Actual initial7977 private Fin3-case API failure remainsNOT_PROVED with exact source/raw; finalb760 strict2/genuine normal1 alone establishPASS.','not_proved':['Interior existence, apex exclusion, False or R1 capacity','F17 contradiction or original all-N sharp lower/prize completion','HIGHapex/LowLB SOURCE_ONLY work'],'publication_file_whitelist':sorted(files),'publication_file_sha256':{p:sha(p) for p in sorted(files) if p!=RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path(STAGE).write_text(json.dumps(sorted(files),indent=2)+'\n');print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'stage_manifest':STAGE,'default_verified_unchanged':2677,'staged':False}))
if __name__=='__main__':main()
