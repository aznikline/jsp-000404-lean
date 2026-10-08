"""Seal checked cyclic incident/actual target budget support; no Lean/Git."""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re
OWNER='research/JSP404_ACTUAL_EMISSION_DEGREE_BUDGET_RECEIPT_20261008.json'
MANIFEST='verification/oct8-actual-emission-degree-budget-publication-files.txt'
BASE='research/JSP404_N4_R2_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
PRIOR='research/JSP404_HIGH_R1_POSITIVE_PROFILE_STANDALONE_RECEIPT_20261008.json'
HERE='.lake/finalize_oct8_emission_budget_standalone.py'
PLAN='.lake/oct8-emission-budget-standalone-prep.json'
RECEIPT='research/JSP404_EMISSION_BUDGET_STANDALONE_RECEIPT_20261008.json'
STAGE='.lake/oct8-emission-budget-standalone-stage-files.json'
OUT=Path('verification/oct8-emission-budget-standalone-review')
DOCS=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOTS=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
FIXED={OWNER:'0e32c2c29fa533ea032c3486992e074d7e95197ebab38c56d38800bacb3b65fb',MANIFEST:'33118c84b5c96b1a4fa9ab6f0b210aa67c07aa16974e455826c3b9b83fc5556f',BASE:'dda4a9cff976557911e827f0f461088c4a6b3c7fdb69fbaf8c69f75c87d28187',PRIOR:'97b35b6e538b80ece97ba735bd6132a8d3bb0365734b9398295e65b754fa6153'}
STD={'propext','Classical.choice','Quot.sound'}
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
    hashes(guards)
    for m in owner['actual_dependency_sources']:meta(m)
    for m in owner['notes']:meta(m)
    files=set(owner['publication_whitelist'])|{MANIFEST};assert len(files)==35
    assert Path(MANIFEST).read_text().splitlines()==owner['publication_whitelist']
    modules={};success=[];failed=[];not_compiled=[];archives=[];warnings={}
    for m in owner['modules']:
        meta(m['source']);meta(m['selected_names']);h=m['source']['sha256']
        modules[m['module']]={'source':m['source']['path'],'source_sha256':h,'selected':m['selected_exports']}
        init=m['initial_not_compiled'];assert init['status']=='NOT_COMPILED_PRECHECK_CANDIDATE' and not init['compiler_failure']
        assert sha(init['snapshot'])==init['sha256'];not_compiled.append(init)
        good={};warnings[m['module']]={}
        for r in m['runs']:
            for k in ['actual_stdout','published_stdout','exact_source_snapshot']:meta(r[k])
            assert not r['guard']['guard_reason'] and r['guard']['source_unchanged']
            raw=Path(r['actual_stdout']['path']).read_bytes();pub=Path(r['published_stdout']['path']).read_bytes()
            assert (gzip.decompress(pub) if r['lossless_gzip'] else pub)==raw
            if r['lossless_gzip']:archives.append({'raw_path':r['actual_stdout']['path'],'raw_sha256':r['actual_stdout']['sha256'],'published_path':r['published_stdout']['path'],'published_sha256':r['published_stdout']['sha256'],'encoding':'gzip','exact_original_byte_restoration':True})
            if r['guard']['exit_code']!=0:
                assert r['status']=='NOT_PROVED_COMPILER_FAILURE' and r['guard']['source_sha256'].startswith('5c344');failed.append({'module':m['module'],**r});continue
            assert r['status']=='PASS_EXACT_SOURCE' and r['guard']['source_sha256']==r['exact_source_snapshot']['sha256']==h
            assert r['selected_standard_axioms_pass']
            ax=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",raw.decode(),re.S))
            for n in m['selected_exports']:assert n in ax and {x.strip() for x in ax[n].split(',') if x.strip()}<=STD,n
            if r['kind']=='normal':assert r['genuine_own_target_built'] and 'Built '+m['module'] in raw.decode() and 'Build completed successfully' in raw.decode()
            else:assert r['kind']=='strict0' and '--trust=0' in r['guard']['command']
            good[r['kind']]=r;warnings[m['module']][r['kind']]={'own':r['own_warning_headers'],'inherited':r['inherited_warning_headers'],'total':r['total_warning_headers']};success.append({'module':m['module'],**r})
        assert set(good)=={'normal','strict0'}
    assert len(modules)==2 and sum(len(m['selected']) for m in modules.values())==2 and len(success)==4 and len(failed)==1 and len(not_compiled)==2
    assert warnings['Jsp000404.RowGainCyclicIncident']['strict0']['own']==warnings['Jsp000404.RowGainCyclicIncident']['normal']['own']==2
    assert warnings['Jsp000404.ActualPositiveGainTargetBudget']['strict0']['own']==warnings['Jsp000404.ActualPositiveGainTargetBudget']['normal']['own']==0
    allowed={**guards,**{m['source']:m['source_sha256'] for m in modules.values()}};queue=[m['source'] for m in modules.values()];seen=set()
    while queue:
        p=queue.pop()
        if p in seen:continue
        assert p in allowed and sha(p)==allowed[p],('unverified dependency',p);seen.add(p)
        for n in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$',Path(p).read_text(),re.M):queue.append(n.replace('.','/')+'.lean')
    assert not any(p.startswith('.lake/') or 'Weighted7977' in p for p in files)
    return owner,base,prior,files,guards,modules,success,failed,not_compiled,archives,warnings
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args();owner,base,prior,files,guards,modules,success,failed,not_compiled,archives,warnings=inputs()
    if a.prepare_only:
        r={'status':'READY_TWO_STANDALONE_EXPORTS_DEFAULT2677_UNCHANGED','modules':modules,'input_file_sha256':{p:sha(p) for p in sorted(files)},'producer_receipt_sha256':FIXED,'finalizer_sha256':sha(HERE),'warning_counts':warnings,'docs_not_read':True,'new_selected_count':2,'standalone_previous':9,'standalone_total':11,'combined_audit_claim':False}
        Path(PLAN).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'plan':PLAN,'sha256':sha(PLAN),'producer_files':len(files),'new_selected':2}));return
    prep=read(PLAN);hashes(prep['input_file_sha256']);assert prep['finalizer_sha256']==sha(HERE)
    OUT.mkdir(parents=True,exist_ok=True);dst=OUT/'finalize_receipt.py'
    if dst.exists():assert dst.read_bytes()==Path(HERE).read_bytes()
    else:dst.write_bytes(Path(HERE).read_bytes())
    files.add(str(dst))
    for p in sorted(files):
        if Path(p).suffix not in ['.txt','.out']:continue
        raw=Path(p).read_bytes()
        if not any(re.search(rb'[ \t]+$',line) for line in raw.splitlines()):continue
        pub=p+'.gz'
        if Path(pub).exists():assert gzip.decompress(Path(pub).read_bytes())==raw
        else:Path(pub).write_bytes(gzip.compress(raw,mtime=0))
        archives.append({'raw_path':p,'raw_sha256':sha(p),'published_path':pub,'published_sha256':sha(pub),'encoding':'gzip','exact_original_byte_restoration':True});files.remove(p);files.add(pub)
    files.update(DOCS);files.add(RECEIPT);selected=[n for m in modules.values() for n in m['selected']]
    paper={p:sha(p) for p in files if 'PAPER' in p or p.endswith('initial-not-compiled.degree-paper.md')}
    r={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SCOPED_STANDALONE_PASS_ACTUAL_POSITIVE_GAIN_TARGET_CARD_FOUR','original_problem_complete':False,'publication_base_commit_reported_by_root':'8d5e8c19a2113e05d408e2486757ba6f7f3fffae','default_gate_unchanged':{'jobs':10935,'verified':2677,'default_selected':2670,'explicit_helpers':7},'base2677_receipt':{'path':BASE,'sha256':FIXED[BASE]},'previous_standalone_receipt':{'path':PRIOR,'sha256':FIXED[PRIOR]},'producer_receipt':{'path':OWNER,'sha256':FIXED[OWNER]},'new_module_count':2,'new_selected_count':2,'modules':modules,'new_selected':selected,'successful_checks':success,'failed_NOT_PROVED_attempts':failed,'not_compiled_precheck_candidates':not_compiled,'standalone_support_outside_default':{'previous':9,'this_batch':2,'total':11,'combined_root_audit_claim':False},'root_sha256':base['root_sha256'],'audit_sha256':base['audit_sha256'],'preserved_prior_sha256':guards,'this_batch_paper_only_sha256':paper,'lossless_stdout_archives':archives,'shared_document_sha256':{p:sha(p) for p in DOCS},'scope':['General sorted distinct full-row indexed erasure merge equals predecessor/successor gapAfter merge, including full wrap/multiplicity.','For any original legal finite planar configuration and arbitrary original observer, pi/5<lambda implies at most4 distinct nonself targets have positive actual rowGain. The actual filter/ordinal/order/incidents are internal; no row score, potential, minimumModel, floor-four, upper-scale or caller arc/order/budget premise.'],'warning_counts':warnings,'warning_policy':'RowGainCyclicIncident retains2 owned style-warning headers in each accepted strict/normal check; child accepted checks have own0. All inherited output retained. No all-owned-warning-free claim.','provenance_policy':'cca1 and86bf are NOT_COMPILED precheck candidates, not compiler failures. Actual5c344 strict1 failure is NOT_PROVED with exact source/raw; final69137 strict2/normal1 and51c4 strict1/normal1 alone establishPASS.','not_proved':['Interior degree3 PAPER refinement','F17 selector/mandatory deletion set/contradiction','General sharp capacity or original all-N lower/prize completion','Weighted7977/newLBconsumer WIP'],'publication_file_whitelist':sorted(files),'publication_file_sha256':{p:sha(p) for p in sorted(files) if p!=RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path(STAGE).write_text(json.dumps(sorted(files),indent=2)+'\n');print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'stage_manifest':STAGE,'default_verified_unchanged':2677,'staged':False}))
if __name__=='__main__':main()
