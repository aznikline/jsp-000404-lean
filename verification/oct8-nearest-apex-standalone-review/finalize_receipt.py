"""Seal independently checked nearest/apex support; no Lean/Git/root edits."""
from pathlib import Path
import argparse, datetime, gzip, hashlib, json, re
BASE='research/JSP404_N4_R2_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
BATCH=Path('verification/oct8-maximal-nearest-unique-zero-apex')
OUT=Path('verification/oct8-nearest-apex-standalone-review')
PLAN='.lake/oct8-nearest-apex-standalone-prep.json'
RECEIPT='research/JSP404_NEAREST_APEX_STANDALONE_RECEIPT_20261008.json'
STAGE='.lake/oct8-nearest-apex-standalone-stage-files.json'
HERE='.lake/finalize_oct8_nearest_apex_standalone.py'
DOCS=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOTS=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
FIXED={BASE:'dda4a9cff976557911e827f0f461088c4a6b3c7fdb69fbaf8c69f75c87d28187',str(BATCH/'nearest/attempt01-receipt.json'):'c0be55d95b357b19070e62f10fff031858e7640ae34329f438b1e5bf3b0bf297',str(BATCH/'apex/attempt01-receipt.json'):'d508d72d137416552ace326d9150eb386f475abac5d5b0caed8a68731628b583'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def hashes(mapping):
    for p,h in mapping.items():assert sha(p)==h,('changed frozen file',p)
def inputs():
    hashes(FIXED);base=read(BASE)
    assert (base['default_build_jobs'],base['composed_standard_axiom_count'])==(10935,2677)
    assert sha(ROOTS[0])==base['root_sha256'] and sha(ROOTS[1])==base['audit_sha256']
    guards={}
    for k in ['preserved_prior_sha256','source_sha256','import_closure_source_sha256','old_paper_only_sha256','new_paper_only_sha256']:guards.update(base[k])
    guards.update({p:h for p,h in base['publication_file_sha256'].items() if p not in DOCS});hashes(guards)
    plan=read(BATCH/'initial-plan.json');hashes(plan['protected_true_parent_sources'])
    assert sha(BATCH/'check_batch.py')==plan['runner_sha256']
    files={str(BATCH/'initial-plan.json'),str(BATCH/'check_batch.py')};modules={};runs=[]
    for target in plan['targets_in_order']:
        key=target['key'];rp=BATCH/key/'attempt01-receipt.json';receipt=read(rp)
        assert receipt['status']=='SCOPED_PASS_TWO_REAL_STAGES' and receipt['all_dispatched_processes_exited']
        assert receipt['source_sha256']==receipt['initial_source_sha256']==target['initial_sha256']==sha(target['source'])
        assert receipt['selected_declarations']==target['selected'] and len(receipt['results'])==2
        modules[receipt['module']]={'source':receipt['source'],'source_sha256':receipt['source_sha256'],'selected':receipt['selected_declarations'],'scope':receipt['scope']}
        files.update([target['source'],target['initial_snapshot'],str(rp)])
        assert sha(target['initial_snapshot'])==target['initial_snapshot_sha256']==receipt['source_sha256']
        for r in receipt['results']:
            assert r['status']=='PASS' and r['exit_code']==0 and r['resource_stop'] is None and r['global_max_Lean_processes']<=1
            assert sha(r['source_snapshot'])==r['source_snapshot_sha256']==r['source_sha256_after']==receipt['source_sha256']
            assert sha(r['log'])==r['log_sha256'];hashes(r['protected_true_parent_sources_after'])
            text=Path(r['log']).read_text();ax=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S))
            for n in target['selected']:assert n in ax and {x.strip() for x in ax[n].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},n
            if r['stage']=='normal':assert r['own_target_built'] and 'Built '+receipt['module'] in text and 'Build completed successfully' in text
            else:assert r['stage']=='strict' and '--trust=0' in r['command']
            runs.append({'module':receipt['module'],**r,'diagnostic_lines_containing_warning_marker':sum('warning:' in l for l in text.splitlines())})
            files.update([r['source_snapshot'],r['log']])
    selected=[n for m in modules.values() for n in m['selected']];assert len(modules)==2 and len(selected)==6 and len(set(selected))==6
    note='research/JSP404_ACTUAL_F17_UNIQUE_ZERO_INTERIOR_APEX_SOURCE_ONLY_20261008.md';files.add(note)
    allowed={**guards,**{m['source']:m['source_sha256'] for m in modules.values()}};seen=set();pending=[m['source'] for m in modules.values()]
    while pending:
        p=pending.pop()
        if p in seen:continue
        assert p in allowed and sha(p)==allowed[p],('unverified dependency',p);seen.add(p)
        for m in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$',Path(p).read_text(),re.M):pending.append(m.replace('.','/')+'.lean')
    return base,modules,selected,files,guards,runs
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args();base,modules,selected,files,guards,runs=inputs()
    if a.prepare_only:
        r={'status':'READY_TWO_MODULES_FOUR_REAL_PASS_STAGES_STANDALONE_ONLY','modules':modules,'new_selected':selected,'new_selected_count':6,'input_file_sha256':{p:sha(p) for p in sorted(files)},'producer_receipt_sha256':FIXED,'root_sha256':base['root_sha256'],'audit_sha256':base['audit_sha256'],'default_gate_unchanged':{'jobs':10935,'verified':2677,'default_selected':2670,'explicit_helpers':7},'finalizer_sha256':sha(HERE),'docs_not_read_until_final_run':True,'Endpoint_SOURCE_ONLY_excluded':True}
        Path(PLAN).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':'READY','plan':PLAN,'sha256':sha(PLAN),'producer_files':len(files),'standalone_selected':6,'default_verified_unchanged':2677}));return
    prep=read(PLAN);hashes(prep['input_file_sha256']);assert prep['finalizer_sha256']==sha(HERE) and prep['modules']==modules
    OUT.mkdir(parents=True,exist_ok=True);dst=OUT/'finalize_receipt.py'
    if dst.exists():assert dst.read_bytes()==Path(HERE).read_bytes()
    else:dst.write_bytes(Path(HERE).read_bytes())
    files.add(str(dst));scope=OUT/'scope.md'
    text='# Independently checked nearest and unique-zero apex support\n\nTwo modules provide six standalone declarations, including the actualClassWeight definition. Their strict and genuine-normal stages passed on unchanged initial source bytes, with no failures and no owned warnings. Default10935/2677 is unchanged; no unified2683 gate is claimed.\n\nNearest: original n>=4 LOW minimumModel, an original maximal row score n-2 and an actual nonacute witness give an original closer point for every distinct target; no caller nearest map/clumps/budget.\n\nApex: original LOW4 Model with exactly one original zero and all other original rows positive supplies the stated original score-one interior/apex facts. A zero apex may remain interior; the hull conclusion is hull-or-zero. The nonacute-heavy exclusion includes its actual nonacute witness. These are scoped necessary structures, not a wholeF17 contradiction or general capacity.\n\nThe historical SOURCE_ONLY note is retained as provenance; actual producer receipts establish the later PASS. Endpoint10d8 and other uncompiled work are excluded. Git publication metadata is tracked separately.\n'
    if scope.exists():assert scope.read_text()==text
    else:scope.write_text(text)
    files.add(str(scope));archives=[]
    for p in sorted(files):
        if Path(p).suffix not in ['.txt','.out']:continue
        raw=Path(p).read_bytes()
        if 'normal' not in Path(p).name and not any(re.search(rb'[ \t]+$',line) for line in raw.splitlines()):continue
        pub=p+'.gz'
        if Path(pub).exists():assert gzip.decompress(Path(pub).read_bytes())==raw
        else:Path(pub).write_bytes(gzip.compress(raw,mtime=0))
        archives.append({'raw_path':p,'raw_sha256':sha(p),'published_path':pub,'published_sha256':sha(pub),'encoding':'gzip','exact_original_byte_restoration':True});files.remove(p);files.add(pub)
    files.update(DOCS);files.add(RECEIPT)
    r={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SCOPED_STANDALONE_PASS_NEAREST_AND_UNIQUE_ZERO_APEX','original_problem_complete':False,'publication_base_commit_reported_by_root':'a8bc93932d311ed0ccf284761e93d3651ff2e818','base_default_receipt':{'path':BASE,'sha256':FIXED[BASE]},'default_gate_unchanged':prep['default_gate_unchanged'],'root_sha256':base['root_sha256'],'audit_sha256':base['audit_sha256'],'new_module_count':2,'new_selected_count':6,'modules':modules,'new_selected':selected,'producer_receipt_sha256':FIXED,'successful_checks':runs,'successful_check_count':4,'failed_attempts':[],'source_unchanged_from_initial':True,'verification_scope':'Independent source strict --trust=0 and genuine own-target normal builds only; no new default/root or combined2683 audit.','preserved_prior_sha256':guards,'old_paper_only_sha256':base['old_paper_only_sha256'],'new_paper_only_sha256':base['new_paper_only_sha256'],'lossless_stdout_archives':archives,'shared_document_sha256':{p:sha(p) for p in DOCS},'scope_note':str(scope),'warning_policy':'Final owned warnings0 in allfourchecks; all inherited diagnostics are retained verbatim. Per-run warning-marker counts are descriptive, not a warning-free claim.','not_proved':['WholeF17 contradiction or mandatory deletion selector','General capacity or original arbitrary-N sharp lower/prize completion','New Endpoint10d8 SOURCE_ONLY'],'publication_file_whitelist':sorted(files),'publication_file_sha256':{p:sha(p) for p in sorted(files) if p!=RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path(STAGE).write_text(json.dumps(sorted(files),indent=2)+'\n');print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'stage_manifest':STAGE,'standalone_selected':6,'default_verified_unchanged':2677,'staged':False}))
if __name__=='__main__':main()
