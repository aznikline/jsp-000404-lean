#!/usr/bin/env python3
"""Build genuine Lake artifacts for the frozen kernel-checked eleven proof.

Model first; at most three independent single-target Lake invocations; terminal
last.  All descendant Lean processes count toward this runner's RSS admission.
No trace, metadata, compiler output, or proof receipt is fabricated.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
from pathlib import Path
import re
import subprocess
import threading
import time

ROOT=Path(__file__).resolve().parents[1]
GIB=1024**3
RECEIPT=ROOT/'research/JSP404_ELEVEN_LAKE_ARTIFACT_RECEIPT_20261005.json'


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def swap_used():
    output=subprocess.check_output(['sysctl','-n','vm.swapusage'],text=True)
    match=re.search(r'used\s*=\s*([\d.]+)([MG])',output)
    return int(float(match.group(1))*(1024**2 if match.group(2)=='M' else GIB)) if match else 0


def build(jobs,rss_gib,resume):
    kernel_path=ROOT/'research/JSP404_ELEVEN_KERNEL_EXPORT_20261005.json'
    kernel=json.loads(kernel_path.read_text())
    checked=kernel['kernel_verification']
    assert checked['trust_level']==0
    assert checked['status']=='PASS' and len(checked['completed_shards'])==624
    assert checked['model']['status']=='PASS' and checked['terminal']['status']=='PASS'
    expected={r['module']:r['source_sha256'] for r in kernel['generated_sources']}
    assert len(expected)==626
    shard_modules={f'NoSatElevenDBMShard{i:03d}' for i in range(624)}
    assert {r['module'] for r in checked['completed_shards']}==shard_modules
    assert set(expected)==shard_modules|{'NoSatElevenDBMModel','NoSatElevenDBMTerminal'}
    for receipt in checked['completed_shards']+[checked['model'],checked['terminal']]:
        assert receipt['status']=='PASS' and receipt['exit_code']==0 and not receipt.get('warnings')
        assert receipt['source_sha256']==expected[receipt['module']]
        assert bool(receipt['axioms']) and set(receipt['axioms'])<={'propext','Classical.choice','Quot.sound'}
        assert Path(receipt['olean']).exists()
    for module,digest in expected.items():
        assert sha(ROOT/'Jsp000404'/f'{module}.lean')==digest,module
    logs=ROOT/'verification/eleven-lake-20261005'
    logs.mkdir(parents=True,exist_ok=True)
    prior=json.loads(RECEIPT.read_text()) if resume and RECEIPT.exists() else {}
    def up_to_date(module):
        result=subprocess.run(['lake','--no-build','build',f'Jsp000404.{module}'],cwd=ROOT,
                              stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
        return result.returncode==0
    retained=[r for r in prior.get('targets',[]) if r['status']=='PASS' and not r.get('warnings') and
              r['source_sha256']==expected.get(r['module']) and Path(r['olean']).exists() and up_to_date(r['module'])]
    report={'status':'RUNNING','verification':'real lake build per target',
            'maximum_parallel_lake_targets':jobs,'own_lean_rss_admission_threshold_gib':rss_gib,
            'targets':retained,'failures':[],'scope':'Model, 624 shards, terminal',
            'kernel_source_receipt':str(kernel_path),'kernel_source_receipt_sha256':sha(kernel_path),
            'source_manifest':expected,'source_sha256':sha(Path(__file__)),
            'actual_geometry_consumers_and_project_root_not_built':True,
            'maximum_observed_own_lean_rss_bytes':0,'maximum_observed_parallel_targets':0,
            'swap_growth_throttled_to_two':False}
    began=time.monotonic()
    initial_swap=swap_used()
    report['initial_system_swap_used_bytes']=initial_swap
    active={};lock=threading.Lock()
    def save():
        report['elapsed_seconds']=round(time.monotonic()-began,3)
        RECEIPT.write_text(json.dumps(report,indent=2)+'\n')
    def rss():
        output=subprocess.check_output(['ps','-axo','pid,ppid,rss,command'],text=True)
        processes={}
        for line in output.splitlines():
            parts=line.strip().split(maxsplit=3)
            if len(parts)==4 and all(s.isdigit() for s in parts[:3]):
                processes[int(parts[0])]=(int(parts[1]),int(parts[2])*1024,parts[3])
        with lock:roots=set(active.values())
        total=0;matched=set()
        for pid,(_,size,command) in processes.items():
            if command.split(maxsplit=1)[0].rsplit('/',1)[-1]!='lean':continue
            cursor=pid;visited=set()
            while cursor in processes and cursor not in visited:
                if cursor in roots:
                    total+=size;matched.add(cursor);break
                visited.add(cursor);cursor=processes[cursor][0]
        report['maximum_observed_own_lean_rss_bytes']=max(report['maximum_observed_own_lean_rss_bytes'],total)
        return total+max(0,len(roots)-len(matched))*int(1.7*GIB)
    def one(module):
        source=ROOT/'Jsp000404'/f'{module}.lean'
        if sha(source)!=expected[module]:
            return {'module':module,'status':'FAIL','reason':'frozen source hash changed'}
        log=logs/f'{module}.txt';started=time.monotonic()
        with log.open('w') as output:
            process=subprocess.Popen(['/usr/bin/time','-l','lake','build',f'Jsp000404.{module}'],cwd=ROOT,
                                     stdout=output,stderr=subprocess.STDOUT)
            with lock:active[module]=process.pid
            try:code=process.wait()
            finally:
                with lock:active.pop(module,None)
        content=log.read_text();unchanged=sha(source)==expected[module]
        groups=re.findall(r"'Jsp404\.NoSatElevenDBMTerminal\.[^']+' depends on axioms:\s*\[([^\]]*)\]",content,re.S)
        axioms=sorted({a.strip() for group in groups for a in group.split(',') if a.strip()})
        warnings=re.findall(r'^.*warning:.*$',content,re.M)
        peak=re.search(r'(\d+)\s+maximum resident set size',content)
        olean=ROOT/'.lake/build/lib/lean/Jsp000404'/f'{module}.olean'
        ok=(code==0 and unchanged and not warnings and olean.exists() and
            set(axioms)<={'propext','Classical.choice','Quot.sound'})
        return {'module':module,'status':'PASS' if ok else 'FAIL','exit_code':code,
                'source_sha256':sha(source),'source_hash_matches_kernel':unchanged,
                'seconds':round(time.monotonic()-started,3),'log':str(log),
                'reported_eleven_point_axioms':axioms,'warnings':warnings,
                'maximum_resident_set_size_bytes':int(peak.group(1)) if peak else None,
                'olean':str(olean)}
    def record(result):
        report['maximum_observed_own_lean_rss_bytes']=max(
            report['maximum_observed_own_lean_rss_bytes'],result.get('maximum_resident_set_size_bytes') or 0)
        report['targets' if result['status']=='PASS' else 'failures'].append(result)
        save()
        print(json.dumps({'lake_progress':True,'target':result['module'],'status':result['status'],
                          'seconds':result.get('seconds'),'completed':len(report['targets']),'of':626,
                          'own_rss_peak_bytes':report['maximum_observed_own_lean_rss_bytes']}),flush=True)
    save()
    if 'NoSatElevenDBMModel' not in {r['module'] for r in retained}:record(one('NoSatElevenDBMModel'))
    if report['failures']:report['status']='FAIL';save();return False
    done={r['module'] for r in report['targets']}
    pending=iter(f'NoSatElevenDBMShard{i:03d}' for i in range(624) if f'NoSatElevenDBMShard{i:03d}' not in done)
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures={}
        def dispatch():
            if swap_used()>initial_swap+256*1024**2:report['swap_growth_throttled_to_two']=True
            maximum=min(jobs,2) if report['swap_growth_throttled_to_two'] else jobs
            while len(futures)<maximum and not report['failures']:
                effective=max(rss(),len(futures)*int(1.7*GIB))
                if effective+int(1.7*GIB)>rss_gib*GIB:break
                module=next(pending,None)
                if module is None:break
                futures[pool.submit(one,module)]=module
                report['maximum_observed_parallel_targets']=max(report['maximum_observed_parallel_targets'],len(futures))
        dispatch()
        while futures:
            finished,_=wait(futures,timeout=1.,return_when=FIRST_COMPLETED)
            rss()
            if not finished:continue
            for future in finished:
                futures.pop(future);record(future.result())
            dispatch()
    finished_modules={r['module'] for r in report['targets']}
    missing=sorted(shard_modules-finished_modules)
    if missing:report['failures'].append({'status':'FAIL','reason':'shards incomplete before terminal','modules':missing})
    if not report['failures'] and 'NoSatElevenDBMTerminal' not in done:record(one('NoSatElevenDBMTerminal'))
    changed=[m for m,d in expected.items() if sha(ROOT/'Jsp000404'/f'{m}.lean')!=d]
    if changed:report['failures'].append({'status':'FAIL','reason':'final frozen source hashes changed','modules':changed})
    report['all_final_source_hashes_match_kernel']=not changed
    complete=(len(report['targets'])==626 and {r['module'] for r in report['targets']}==set(expected))
    report['status']='PASS' if complete and not report['failures'] else 'FAIL'
    save()
    print(json.dumps({'lake_artifacts_status':report['status'],'verified_targets':len(report['targets']),
                      'elapsed_seconds':report['elapsed_seconds']}),flush=True)
    return report['status']=='PASS'


if __name__=='__main__':
    if not __debug__:raise RuntimeError('frozen receipt checks require assertions enabled')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs',type=int,choices=(1,2,3),default=3)
    parser.add_argument('--own-rss-gib',type=float,default=6.)
    parser.add_argument('--resume',action='store_true')
    args=parser.parse_args()
    assert 1.7<=args.own_rss_gib<=6
    raise SystemExit(0 if build(args.jobs,args.own_rss_gib,args.resume) else 1)
