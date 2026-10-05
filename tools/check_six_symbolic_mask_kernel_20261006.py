#!/usr/bin/env python3
"""Real staged single-process compiler/Lake checks for a new orientation sample."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,time
from check_six_symbolic_kernel_20261005 import rss_tree,STANDARD
ROOT=Path(__file__).resolve().parents[1]
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--mask',type=int,default=567);ap.add_argument('--stage',choices=['nat','actual','reflection','normal'],required=True);ap.add_argument('--seconds',type=float,default=420);args=ap.parse_args();mask=args.mask;assert mask!=0
 path=ROOT/f'research/JSP404_SIX_SYMBOLIC_M{mask}_NAT_SHARDS_MANIFEST_20261006.json';manifest=json.loads(path.read_text())
 wrapper={'module':f'Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}Integer','source':f'Jsp000404/SixExactFloorKernelSymbolicMask{mask:03d}Integer.lean'}
 actual={'module':f'Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}Probe','source':f'Jsp000404/SixExactFloorKernelSymbolicMask{mask:03d}Probe.lean'}
 reflection={'module':f'Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}Reflection','source':f'Jsp000404/SixExactFloorKernelSymbolicMask{mask:03d}Reflection.lean'}
 targets=manifest['shards']+[wrapper] if args.stage=='nat' else [actual] if args.stage=='actual' else [reflection] if args.stage=='reflection' else manifest['shards']+[wrapper,actual,reflection]
 logdir=ROOT/f'verification/six-symbolic-mask{mask}-{args.stage}-20261006';logdir.mkdir(exist_ok=True)
 receiptpath=ROOT/f'research/JSP404_SIX_SYMBOLIC_M{mask}_{args.stage.upper()}_RECEIPT_20261006.json';receipt=json.loads(receiptpath.read_text()) if receiptpath.exists() else {'status':'RUNNING','stage':args.stage,'mask':mask,'concurrency':1,'results':[]};recorded={r['module']:r for r in receipt['results']}
 for target in targets:
  source=ROOT/target['source'];sha=hashlib.sha256(source.read_bytes()).hexdigest()
  if 'source_sha256' in target:assert sha==target['source_sha256']
  artifact=ROOT/'.lake/build/lib/lean'/Path(target['source']).with_suffix('.olean');old=recorded.get(target['module'])
  if old and old['status']=='PASS' and old['source_sha256']==sha and artifact.exists() and hashlib.sha256(artifact.read_bytes()).hexdigest()==old['artifact_sha256']:continue
  cap=8 if target['module'].endswith(('Probe','Reflection')) else 6
  command=['lake','build',target['module']] if args.stage=='normal' else ['lake','env','lean','--trust=0','-DautoImplicit=false','-o',str(artifact),str(source)]
  log=logdir/f'{target["module"].rsplit(".",1)[1]}.txt';start=time.monotonic();peak=0;stop=None
  with log.open('w') as output:
   proc=subprocess.Popen(command,cwd=ROOT,stdout=output,stderr=subprocess.STDOUT)
   while proc.poll() is None:
    rss,rows,own=rss_tree(proc.pid);peak=max(peak,rss)
    if rss>=cap*1024**2 or time.monotonic()-start>args.seconds:
     stop='RSS_CAP' if rss>=cap*1024**2 else 'TIME_CAP'
     for pid in [pid for pid,parent,rss in rows if pid in own and not any(pp==pid for cc,pp,rr in rows)]:subprocess.run(['kill','-INT',str(pid)],check=False)
     break
    time.sleep(.1)
   proc.wait(timeout=20)
  text=log.read_text();axioms=re.findall(r'depends on axioms: \[([^\]]*)\]',text)
  ok=proc.returncode==0 and not stop and 'error:' not in text and artifact.exists() and (args.stage=='normal' or axioms) and all(set(a.replace(',',' ').split()).issubset(STANDARD) for a in axioms)
  r={'module':target['module'],'source':target['source'],'source_sha256':sha,'status':'PASS' if ok else 'NOT_PROVED','exit_code':proc.returncode,'resource_stop':stop,'rss_cap_gib':cap,'seconds':time.monotonic()-start,'sampled_peak_tree_rss_kib':peak,'command':command,'log':str(log.relative_to(ROOT)),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'axioms':axioms,'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest() if ok else None}
  receipt['results']=[old for old in receipt['results'] if old['module']!=r['module']]+[r];receipt['completed']=sum(x['status']=='PASS' for x in receipt['results']);receipt['status']='RUNNING' if ok else 'NOT_PROVED';receiptpath.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:r[k] for k in ('module','status','seconds','sampled_peak_tree_rss_kib')}),flush=True)
  if not ok:raise RuntimeError(f'{target["module"]} did not pass; dispatch stopped')
 receipt['status']='PASS';receipt['expected_targets']=len(targets);receiptpath.write_text(json.dumps(receipt,indent=2)+'\n')
if __name__=='__main__':main()
