"""Freeze this verified support bundle only after Root's real composed gates.
--prepare-only writes a private input manifest without reading mutable docs.
No Lean/Git execution and no Root/Audit/source edits.
"""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re
PREP=Path('.lake/oct8-weighted-final-prep/prep.json')
OUT=Path('verification/oct8-weighted-support-review')
RECEIPT='research/JSP404_WEIGHTED_F18_F17_SUPPORT_INTEGRATION_RECEIPT_20261008.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def add_dir(files,path):
    files.update(str(p) for p in Path(path).rglob('*') if p.is_file() and not p.name.endswith(('.olean','.ilean','.trace','.pyc')) and '__pycache__' not in str(p))
def inputs():
    prep=read(PREP);base=read(prep['base_integration_receipt']['path'])
    assert sha(prep['base_integration_receipt']['path'])==prep['base_integration_receipt']['sha256']
    for p,h in base['preserved_tracked_lean_sha256'].items():assert sha(p)==h,p
    assert sha('Jsp000404.lean')==prep['root_after_sha256']
    assert sha('verification/oct5-review/ProofAudit.lean')==prep['audit_after_sha256']
    original=read('.lake/oct8-weighted-catalog-publication-prep.json')
    files=set(original['existing_source_evidence_whitelist'])
    for p,h in original['existing_source_evidence_sha256'].items():assert sha(p)==h,p
    receipt_paths=[v['producer_evidence'] for v in original['modules'].values()]
    for rp in ['research/JSP404_ACTUAL_N4_R2_CAPACITY_FROM_CRIT22_RECEIPT_20261008.json',
               'research/JSP404_ACTUAL_N4_R2_CRITICAL22_ADAPTER_RECEIPT_20261008.json',
               'research/JSP404_ACTUAL_F18_UNIQUE_HEAVY_SINGLETON_RECEIPT_20261008.json',
               'research/JSP404_ACTUAL_F18_UNIQUE_HEAVY_ACUTE_RECEIPT_20261008.json']:
        d=read(rp);receipt_paths.append(rp);files.add(rp)
        src=d['source'];assert sha(src['path'])==src['sha256'];files.add(src['path'])
        for k in ['research_note','historical_source_only_note','selected_names','raw_runs_record']:
            v=d.get(k)
            if isinstance(v,dict):assert sha(v['path'])==v['sha256'];files.add(v['path'])
        for k in ['publication_file_whitelist','publication_whitelist']:
            files.update(d.get(k,[]))
        if 'publication_file_sha256' in d:
            for p,h in d['publication_file_sha256'].items():assert sha(p)==h,p
    directories=['verification/oct8-actual-n4-r2-capacity-from-crit22',
      'verification/oct8-actual-n4-r2-critical22-adapter','verification/oct8-actual-f18-unique-heavy-singleton',
      'verification/oct8-actual-f18-unique-heavy-acute','verification/oct8-devin-f17-hull-gap-local',
      'verification/oct8-devin-f18-two-heavy-local','verification/oct8-devin-f17-selector-local',
      'verification/devin-f17-hull-gap-20261008','verification/devin-f17-selector-20261008']
    for path in directories:assert Path(path).is_dir(),path;add_dir(files,path)
    for module,selected_count in [('DevinF17HullGap',14),('DevinF18TwoHeavyApex',7),('DevinF17Selector',8)]:
        source='Jsp000404/'+module+'.lean';files.add(source)
        directory={'DevinF17HullGap':'oct8-devin-f17-hull-gap-local','DevinF18TwoHeavyApex':'oct8-devin-f18-two-heavy-local','DevinF17Selector':'oct8-devin-f17-selector-local'}[module]
        vd=Path('verification')/directory;cp=read(vd/'checkpoint.json');assert cp['status'] in ['PASS','PASS_ALL_14']
        assert sha(vd/'check.py')==cp['runner_sha256']
        for r in cp['attempts']:
            assert r['status']=='PASS' and r['exit_code']==0 and r.get('resource_stop') is None
            assert sha(r['source_snapshot'])==r['source_snapshot_sha256']
            assert sha(r['stdout'])==r['stdout_sha256']
            if r['stage'] in ['strict','normal']:assert r['source_sha256']==sha(source)
            if r['stage']=='normal':assert r['own_target_built']
        receipt_paths.append(str(vd/'RECEIPT.md'));assert (vd/'RECEIPT.md').is_file()
        exports=read(vd/'final-result.json')['all_public_theorem_exports']
        assert (exports if isinstance(exports,int) else len(exports))==selected_count
    for path in ['research/DEVIN_F17_SELECTOR_20261008.md','research/JSP404_F17_HULL_ZERO_SELECTOR_AUDIT_OCT8.md','research/DEVIN_F18_TWO_HEAVY_20261008.md']:
        if Path(path).exists():files.add(path)
    # Local proof acceptance supersedes the partial cloud audit, preserving history unchanged.
    sources={str(Path('Jsp000404')/(m+'.lean')) for m in ['ActualF18ClassWeight','ActualF18InteriorApex','ActualHeavyClumpWeight','ActualF18NonacuteApex','SixOuterWordCatalogComplete','ActualN4R2CapacityAssembly','ActualN4R2CapacityFromCrit22','ActualN4R2Critical22Adapter','ActualF18UniqueHeavySingleton','ActualF18UniqueHeavyAcute','DevinF17HullGap','DevinF18TwoHeavyApex','DevinF17Selector']}
    assert len(sources)==13;files.update(sources)
    allowed=set(base['import_closure_source_sha256'])|sources
    seen=set();todo=['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']
    while todo:
        p=todo.pop()
        if p in seen:continue
        seen.add(p)
        for m in re.findall(r'^import\s+(Jsp000404(?:\.\w+)*)\s*$',Path(p).read_text(),re.M):
            q=m.replace('.','/')+'.lean';assert q in allowed,('unverified import',p,q);todo.append(q)
    paper=read('research/JSP404_F17_F18_LOCAL_CONSUMERS_RECEIPT_20261007.json')['paper_only_sha256']
    for p,h in paper.items():assert sha(p)==h,p
    assert len(paper)==8
    return prep,base,files,receipt_paths,sources,seen,paper

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare-only',action='store_true');args=ap.parse_args()
    prep,base,files,producer_paths,sources,closure,paper=inputs()
    if args.prepare_only:
        target=Path('.lake/oct8-weighted-final-prep/publication-plan.json')
        target.write_text(json.dumps({'status':'INPUTS_READY_COMPOSED_GATES_NOT_CLAIMED','modules':13,'new_selected':61,'requested_verified':2200,'files':sorted(files),'file_hashes':{p:sha(p) for p in sorted(files)},'source_sha256':{p:sha(p) for p in sorted(sources)},'mutable_docs_not_read':True},indent=2)+'\n')
        print(json.dumps({'status':'READY','manifest':str(target),'sha256':sha(target),'input_files':len(files),'sources':13}));return
    full=read(OUT/'full.json');audit=read(OUT/'audit.json');gates=read(OUT/'gates.json')
    assert full['exit_code']==audit['exit_code']==0
    for r in [full,audit]:assert sha(r['stdout'])==r['stdout_sha256'] and not r['rss_cap_killed'] and not r['timeout_killed']
    assert gates[0]['exit_code']==0 and gates[0]['declaration_count']==2200 and not gates[0]['failures']
    assert gates[1]['exit_code']==1 and gates[1]['failures']==[{'declaration':'Jsp404.sendov_lower','unexpected_axioms':['sorryAx']}]
    for r in gates:assert sha(r['stdout'])==r['stdout_sha256']
    jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',Path(full['stdout']).read_text()).group(1));assert jobs==10889
    verified=read(gates[0]['stdout'])['axioms'];assert all(n in verified for n in prep['new_selected'])
    assert len(prep['new_selected'])==len(set(prep['new_selected']))==61
    # Shared mutable prose is read/frozen only at this final invocation, after Root updates it.
    docs=['notes/STATUS.md','research/JSP404_ACTUAL_N4_IMPLEMENTATION_HANDOFF_20261007.md']
    files.update(docs);files.update(['Jsp000404.lean','verification/oct5-review/ProofAudit.lean']);add_dir(files,OUT)
    for src,dst in [('.lake/run_oct8_weighted_bundle.py',OUT/'run_checks.py'),('.lake/check_oct8_weighted_bundle_gates.py',OUT/'check_gates.py'),('.lake/finalize_oct8_weighted_bundle.py',OUT/'finalize_receipt.py')]:
        dst.write_bytes(Path(src).read_bytes());files.add(str(dst))
    archives=[]
    for p in sorted(files):
        q=Path(p)
        if q.suffix not in ['.txt','.out','.log','.py']:continue
        raw=q.read_bytes();trailing=any(re.search(rb'[ \t]+$',line) for line in raw.splitlines())
        # Preserve every normal stdout losslessly; old ignored .log copies get explicit published paths.
        compress=trailing or 'normal' in q.name or 'build' in q.name
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
    assert not any('SixWeakOuter' in p or 'SixDoubleLow' in p or 't3draft' in p for p in files)
    files.add(RECEIPT)
    r=dict(recorded_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='SCOPED_PASS_WEIGHTED_F18_AND_F17_TOOLS_ORIGINAL_LOWER_OPEN',original_problem_complete=False,
      publication_base_integration_receipt=prep['base_integration_receipt'],
      new_modules=sorted(sources),new_selected=prep['new_selected'],new_selected_count=61,
      composed_standard_axiom_count=2200,default_root_selected_count=2193,existing_explicit_helpers=7,default_build_jobs=jobs,
      full_build=full,composed_trust_zero_audit=audit,standard_axiom_gate=gates[0],original_root_negative_gate=gates[1],
      source_sha256={p:sha(p) for p in sorted(sources)},preserved_tracked_lean_sha256=base['preserved_tracked_lean_sha256'],
      import_closure_source_sha256={p:sha(p) for p in sorted(closure)},paper_only_sha256=paper,
      producer_receipts_sha256={p:sha(p) for p in producer_paths},root_sha256=sha('Jsp000404.lean'),audit_sha256=sha('verification/oct5-review/ProofAudit.lean'),shared_document_sha256={p:sha(p) for p in docs},lossless_stdout_archives=archives,
      scope=['Weighted original F18 class weights, interior apex geometry/disjointness, heavy clump weights and nonacute exclusion.',
             'Whole original F18 unique-heavy and two-heavy branches are excluded. All-light was previously excluded; three-heavy remains outside this batch.',
             'Actual GenericModel5 n4 word membership in62 masks, without HIGH/profile/acyclic/callback; no weak/double all62 exclusion.',
             'Conditional original n4 R2 capacity/critical22 adapter implications; A/B scalar exclusions remain explicit unfilled hypotheses.',
             'F17 original hull-zero outside-gap plateau and boundary/window helpers; independent local strict/normal and full14-export audit complete current validation; historical cloud8 scope and missing early failure snapshots remain unchanged. Selector8 is not mandatory SEL or F17 contradiction.'],
      warning_policy='All own/inherited warning bytes retained, including actual local Gap/T2/Selector warnings and conditional Assembly warnings. No warning-free claim or warning-only rebuild.',
      failed_output_policy='Original failed snapshots and raw stdout stay NOT_PROVED. Early cloud candidates not preserved are not reconstructed; historical prepared provenance is not current acceptance.',
      not_proved=['Mandatory F17 hull-zero deletion selector or complete F17 exclusion','Whole F18 three-heavy branch in this selected bundle; new standalone work is tracked separately','Unconditional actual F22/fullR2 capacity without A/B closures','Original arbitrary-N sharp lower theorem','Complete prize submission'],
      excluded=['Three-heavy/WholeF18 new modules outside this batch, and unproved weak/double variants','Uncompiled cloud code other than explicitly locally verified sources'],
      publication_file_whitelist=sorted(files),publication_file_sha256={p:sha(p) for p in sorted(files) if p!=RECEIPT})
    Path(RECEIPT).write_text(json.dumps(r,indent=2)+'\n')
    Path('.lake/oct8-weighted-final-prep/stage-files.json').write_text(json.dumps(sorted(files),indent=2)+'\n')
    print(json.dumps({'receipt':RECEIPT,'sha256':sha(RECEIPT),'files':len(files),'composed':2200,'staged':False}))
if __name__=='__main__':main()
