"""Seal checked unique-zero narrow-hull targets; no Lean/Git/root edits."""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re
OWNER='research/JSP404_ACTUAL_F17_UNIQUE_ZERO_NARROW_HULL_TARGETS_RECEIPT_20261008.json'
MANIFEST='verification/oct8-f17-unique-zero-narrow-hull-targets-publication-files.txt'
BASE='research/JSP404_N4_R2_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
PRIOR='research/JSP404_HIGH_R1_CLASS_WEIGHT_STANDALONE_RECEIPT_20261008.json'
HERE='.lake/finalize_oct8_narrow_targets_standalone.py'
PLAN='.lake/oct8-narrow-targets-standalone-prep.json'
RECEIPT='research/JSP404_NARROW_HULL_TARGETS_STANDALONE_RECEIPT_20261008.json'
STAGE='.lake/oct8-narrow-targets-standalone-stage-files.json'
OUT=Path('verification/oct8-narrow-targets-standalone-review')
DOCS=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOTS=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
FIXED={OWNER:'44e5b5b4fa61828a4a8d72a77cb4939e893a1599bbdc54882d200e36c1827fa1',MANIFEST:'c04b03ac0ad555621a64e826cc75a94b33cb1f0c811a91c3c37b173aaba7701d',BASE:'dda4a9cff976557911e827f0f461088c4a6b3c7fdb69fbaf8c69f75c87d28187',PRIOR:'a3a7f036c05ed5ece2bee9c023b125d7abbf8e3e0ab7fb09504fe283b571abbd'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def hashes(m):
    for p,h in m.items():assert sha(p)==h,('changed frozen file',p)
def meta(m):assert sha(m['path'])==m['sha256'],m['path']
def inputs():
    hashes(FIXED);owner,base,prior=read(OWNER),read(BASE),read(PRIOR)
    assert (base['default_build_jobs'],base['composed_standard_axiom_count'])==(10935,2677)
    assert sha(ROOTS[0])==base['root_sha256'] and sha(ROOTS[1])==base['audit_sha256']
    guards=dict(prior['preserved_prior_sha256'])
    for r in [base,prior]:guards.update({p:h for p,h in r['publication_file_sha256'].items() if p not in DOCS})
    hashes(guards);meta(owner['source'])
    for m in owner['true_parent_sources_initial_and_final_matching']:meta(m)
    files=set(owner['publication_whitelist'])|{MANIFEST};assert len(files)==17
    assert Path(MANIFEST).read_text().splitlines()==owner['publication_whitelist']
    assert owner['source']['sha256']=='354d8a5911424c80aaf70a9a298852173b3e6e7f376dcc9389b638216628f959'
    assert owner['selected_count']==1 and owner['failed_attempt_count']==1
    success=[];failed=[];archives=[]
    for r in owner['runs']:
        for k in ['actual_stdout','published_stdout','exact_source_snapshot']:meta(r[k])
        assert not r['guard']['guard_reason'] and r['guard']['source_unchanged']
        raw=Path(r['actual_stdout']['path']).read_bytes();pub=Path(r['published_stdout']['path']).read_bytes()
        assert (gzip.decompress(pub) if r['lossless_gzip'] else pub)==raw
        if r['lossless_gzip']:archives.append({'raw_path':r['actual_stdout']['path'],'raw_sha256':r['actual_stdout']['sha256'],'published_path':r['published_stdout']['path'],'published_sha256':r['published_stdout']['sha256'],'encoding':'gzip','exact_original_byte_restoration':True})
        if r['guard']['exit_code']!=0:
            assert r['status']=='NOT_PROVED_COMPILER_FAILURE' and r['guard']['source_sha256'].startswith('59b9');failed.append(r);continue
        assert r['status']=='PASS_EXACT_SOURCE' and r['guard']['source_sha256']==r['exact_source_snapshot']['sha256']==owner['source']['sha256']
        assert r['selected_standard_axioms_pass']
        ax=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",raw.decode(),re.S))
        for n in owner['selected_exports']:assert n in ax and {x.strip() for x in ax[n].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},n
        if r['kind']=='normal':assert r['genuine_own_target_built'] and 'Built '+owner['module'] in raw.decode() and 'Build completed successfully' in raw.decode()
        else:assert '--trust=0' in r['guard']['command']
        success.append(r)
    assert len(success)==2 and len(failed)==1
    allowed={**guards,owner['source']['path']:owner['source']['sha256']};queue=[owner['source']['path']];seen=set()
    while queue:
        p=queue.pop()
        if p in seen:continue
        assert p in allowed and sha(p)==allowed[p],('unverified dependency',p);seen.add(p)
        for n in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$',Path(p).read_text(),re.M):queue.append(n.replace('.','/')+'.lean')
    assert not any('HighR1InteriorApex' in p or p.startswith('.lake/') for p in files)
    return owner,base,prior,files,guards,success,failed,archives
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args();owner,base,prior,files,guards,success,failed,archives=inputs()
    if a.prepare_only:
        r={'status':'READY_NARROW_TARGETS_STANDALONE_ONLY','input_file_sha256':{p:sha(p) for p in sorted(files)},'producer_receipt_sha256':FIXED,'finalizer_sha256':sha(HERE),'selected_count':1,'standalone_previous':12,'standalone_total':13,'default_verified_unchanged':2677,'docs_not_read':True}
        Path(PLAN).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'plan':PLAN,'sha256':sha(PLAN),'producer_files':len(files),'selected':1}));return
    prep=read(PLAN);hashes(prep['input_file_sha256']);assert prep['finalizer_sha256']==sha(HERE)
    OUT.mkdir(parents=True,exist_ok=True);dst=OUT/'finalize_receipt.py'
    if dst.exists():assert dst.read_bytes()==Path(HERE).read_bytes()
    else:dst.write_bytes(Path(HERE).read_bytes())
    files.add(str(dst));files.update(DOCS);files.add(RECEIPT)
    r={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SCOPED_STANDALONE_PASS_UNIQUE_ZERO_NARROW_HULL_LIGHT_TARGETS','original_problem_complete':False,'publication_base_commit_reported_by_root':'0fcb5a0c0987a2f20fecc107bc1bd83ec5118936','default_gate_unchanged':{'jobs':10935,'verified':2677,'default_selected':2670,'explicit_helpers':7},'base2677_receipt':{'path':BASE,'sha256':FIXED[BASE]},'previous_standalone_receipt':{'path':PRIOR,'sha256':FIXED[PRIOR]},'producer_receipt':{'path':OWNER,'sha256':FIXED[OWNER]},'new_module_count':1,'new_selected_count':1,'new_selected':owner['selected_exports'],'source':owner['source'],'successful_checks':success,'failed_NOT_PROVED_attempts':failed,'standalone_support_outside_default':{'previous':12,'this_batch':1,'total':13,'combined_root_audit_claim':False},'root_sha256':base['root_sha256'],'audit_sha256':base['audit_sha256'],'preserved_prior_sha256':guards,'lossless_stdout_archives':archives,'shared_document_sha256':{p:sha(p) for p in DOCS},'scope':owner['scope'],'warning_policy':'Final owned warnings0; all469 inherited normal headers retained verbatim in lossless gzip. No whole-output-warning-free claim.','failure_policy':'Initial59b9 source actually failed strict1 and remainsNOT_PROVED, notNOT_COMPILED. Final354d strict2/genuine normal1 alone establishPASS.','not_proved':['B nonempty, every lightHull target narrow, or original zeroHull','F17False/mandatory selector or general capacity','Original all-N lower/prize completion','HIGHapex5e74 SOURCE_ONLY'],'publication_file_whitelist':sorted(files),'publication_file_sha256':{p:sha(p) for p in sorted(files) if p!=RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path(STAGE).write_text(json.dumps(sorted(files),indent=2)+'\n');print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'stage_manifest':STAGE,'default_verified_unchanged':2677,'staged':False}))
if __name__=='__main__':main()
