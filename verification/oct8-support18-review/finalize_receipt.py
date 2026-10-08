"""Seal composed actual support checks and retained producer history; no Lean/Git."""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re
PREP='.lake/oct8-support18-draft.json'
PLAN='.lake/oct8-support18-publication-plan.json'
RECEIPT='research/JSP404_ACTUAL_SUPPORT18_INTEGRATION_RECEIPT_20261008.json'
STAGE='.lake/oct8-support18-stage-files.json'
BASE='research/JSP404_N4_R2_COMPLETE_INTEGRATION_RECEIPT_20261008.json'
HIGH='verification/oct8-high-r1-interior-apex/receipt.json'
OUT=Path('verification/oct8-support18-review')
DOCS=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
ROOTS=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
STD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def hashes(m):
    for p,h in m.items():assert sha(p)==h,('changed frozen file',p)
def inputs():
    prep,base=read(PREP),read(BASE)
    assert prep['status']=='READY_PRODUCERS_ROOT_AUTHORIZED' and not prep['pending_modules']
    assert sha(ROOTS[0])==prep['root_after_sha256'] and sha(ROOTS[1])==prep['audit_after_sha256']
    hashes(prep['new_source_sha256']);hashes(prep['producer_receipt_sha256'])
    assert len(prep['modules'])==9 and len(set(prep['new_selected']))==18
    guards={}
    for k in ['preserved_prior_sha256','source_sha256','import_closure_source_sha256','old_paper_only_sha256','new_paper_only_sha256']:guards.update(base[k])
    guards.update({p:h for p,h in base['publication_file_sha256'].items() if p not in ROOTS+DOCS})
    guards={p:h for p,h in guards.items() if p not in ROOTS+DOCS};hashes(guards)
    files=set();paper={}
    for path in prep['producer_receipt_sha256']:
        if path==HIGH:continue
        r=read(path);hashes({p:h for p,h in r['publication_file_sha256'].items() if p not in DOCS})
        files.update(set(r['publication_file_whitelist'])-set(DOCS))
        for k,v in r.items():
            if 'paper_only_sha256' in k and isinstance(v,dict):paper.update(v)
    high=read(HIGH);assert high['status']=='READY' and high['all_lean_lake_exited_before_formal_return']
    assert high['source_sha256']==prep['new_source_sha256'][high['source']]
    assert high['own_warning_headers']==1 and high['normal_inherited_warning_headers']==22224
    hashes(high['parents_current_sha256']);files.add(HIGH)
    for f in high['publication_files']:assert sha(f['path'])==f['sha256'];files.add(f['path'])
    for family in ['strict_reuse_records','normal_reuse_records']:
        assert len(prep[family])==9
        for module,r in prep[family].items():
            assert sha(r['producer_path'])==r['producer_sha256']
            assert sha(r['snapshot'])==r['snapshot_sha256']==r['source_sha256'] and sha(r['stdout'])==r['stdout_sha256']
            text=Path(r['stdout']).read_text();ax=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S))
            assert all(n in ax and {x.strip() for x in ax[n].split(',') if x.strip()}<=STD for n in r['selected']),module
    assert not any(p.startswith('.lake/') or '/diagnostic' in p or 'scalar-unsat' in p for p in files)
    return prep,base,files,guards,paper,high
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args();prep,base,files,guards,paper,high=inputs()
    if a.prepare_only:
        r={'status':'PRODUCERS_READY_COMPOSED_GATES_PENDING','producer_files':sorted(files),'producer_file_sha256':{p:sha(p) for p in sorted(files)},'new_modules':9,'new_selected':18,'requested_verified':2695,'requested_default':2688,'root_sha256':prep['root_after_sha256'],'audit_sha256':prep['audit_after_sha256'],'docs_not_read':True,'warning_policy':prep['warning_policy']}
        Path(PLAN).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'plan':PLAN,'sha256':sha(PLAN),'producer_files':len(files)}));return
    plan=read(PLAN);hashes(plan['producer_file_sha256'])
    full,audit,gates=read(OUT/'full.json'),read(OUT/'audit.json'),read(OUT/'gates.json')
    for r in [full,audit]:
        assert r['exit_code']==0 and not r['rss_cap_killed'] and not r['timeout_killed'] and not r['parallel_lean_cap_killed'] and r['max_global_lean_count']<=1
        assert sha(r['stdout'])==r['stdout_sha256']
    assert gates[0]['exit_code']==0 and gates[0]['declaration_count']==2695 and not gates[0]['failures']
    assert gates[1]['exit_code']==1 and gates[1]['failures']==[{'declaration':'Jsp404.sendov_lower','unexpected_axioms':['sorryAx']}]
    for r in gates:assert sha(r['stdout'])==r['stdout_sha256']
    ax=read(gates[0]['stdout'])['axioms'];assert all(n in ax and set(ax[n])<=STD for n in prep['new_selected'])
    jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',Path(full['stdout']).read_text()).group(1))
    files.update(ROOTS+DOCS);files.update(str(OUT/p) for p in ['root-before.lean','audit-before.lean','full.json','full.stdout.txt','audit.json','audit.stdout.txt','gates.json','verified-gate.json','root-gate.json'])
    for src,name in [('.lake/run_oct8_support18_bundle_draft.py','run_checks.py'),('.lake/check_oct8_support18_bundle_gates_draft.py','check_gates.py'),('.lake/finalize_oct8_support18_bundle.py','finalize_receipt.py')]:
        dst=OUT/name
        if dst.exists():assert dst.read_bytes()==Path(src).read_bytes()
        else:dst.write_bytes(Path(src).read_bytes())
        files.add(str(dst))
    archives=[]
    for path in prep['producer_receipt_sha256']:
        if path!=HIGH:archives.extend(read(path).get('lossless_stdout_archives',[]))
    for p in sorted(files):
        if Path(p).suffix not in ['.txt','.out']:continue
        raw=Path(p).read_bytes()
        if 'normal' not in Path(p).name and 'full' not in Path(p).name and not any(re.search(rb'[ \t]+$',line) for line in raw.splitlines()):continue
        pub=p+'.gz'
        if Path(pub).exists():assert gzip.decompress(Path(pub).read_bytes())==raw
        else:Path(pub).write_bytes(gzip.compress(raw,mtime=0))
        archives.append({'raw_path':p,'raw_sha256':sha(p),'published_path':pub,'published_sha256':sha(pub),'encoding':'gzip','exact_original_byte_restoration':True});files.remove(p);files.add(pub)
    files.add(RECEIPT)
    r={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SCOPED_PASS_COMPOSED_ACTUAL_SUPPORT18_ORIGINAL_LOWER_OPEN','original_problem_complete':False,'base2677_receipt':{'path':BASE,'sha256':sha(BASE)},'producer_receipt_sha256':prep['producer_receipt_sha256'],'new_module_count':9,'new_selected_count':18,'modules':prep['modules'],'new_selected':prep['new_selected'],'composed_standard_axiom_count':2695,'default_root_selected_count':2688,'existing_explicit_helpers':7,'default_build_jobs':jobs,'full_build':full,'composed_trust_zero_audit':audit,'standard_axiom_gate':gates[0],'original_root_negative_gate':gates[1],'source_sha256':prep['new_source_sha256'],'normal_reuse_records':prep['normal_reuse_records'],'strict_reuse_records':prep['strict_reuse_records'],'preserved_prior_sha256':guards,'import_closure_source_sha256':prep['candidate_import_closure_source_sha256'],'paper_only_sha256':paper,'root_sha256':sha(ROOTS[0]),'audit_sha256':sha(ROOTS[1]),'shared_document_sha256':{p:sha(p) for p in DOCS},'lossless_stdout_archives':archives,'scope':['The thirteen prior standalone declarations and five newly checked HIGH apex declarations are now loaded by default and accepted in the2695 composed standard-axiom gate.','Generic actual positive-gain target degree<=4 above pi/5, scoped actual nearest witnesses, LOW unique-zero narrowHullLight common-observer targets, and LOW/HIGH conditional interior/apex/class-weight structures retain their precise original premises.','HIGH cap20 originalModel+SAT+score2+explicitallpositive internally gives canonicalclasses, mutualnonapex, originalHull apex/disjointness and originalinteriorcount<=3. Positivity remains explicit; no R1capacity or general positivity result.','Already verified n4 HIGH R2 capacity remains intact; original F17 contradiction and arbitrary-N lower remain open.'],'warning_policy':prep['warning_policy'],'warning_details':{'HighApex':{'owned_per_accepted_stage':1,'normal_inherited':22224,'retained':'dif_pos deprecated'},'RowGainCyclicIncident':{'owned_per_accepted_stage':2}},'failure_policy':'Retain all prior failures, including HighApex initial5e74, weighted7977, narrow59b9, profile6c5e and endpoint10d8/7e80. Each exact source/raw remainsNOT_PROVED. cca1/86bf remainNOT_COMPILED, not compiler failures. No output stripping.','not_proved':['F17False, Bnonempty/allLHnarrow, or mandatory deletion selector','CompleteHIGH R1/R0 or general sharp capacity','Original arbitrary-N lower/prize completion','Scalar UNSAT diagnostics are not proof declarations'],'publication_file_whitelist':sorted(files),'publication_file_sha256':{p:sha(p) for p in sorted(files) if p!=RECEIPT}}
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n');Path(STAGE).write_text(json.dumps(sorted(files),indent=2)+'\n');print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'stage_manifest':STAGE,'verified':2695,'full_jobs':jobs,'staged':False}))
if __name__=='__main__':main()
