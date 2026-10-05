#!/usr/bin/env python3
"""Sequential real strict compiler or Lake checks with a process-tree RSS guard."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,time
ROOT=Path(__file__).resolve().parents[1]
STANDARD={'propext','Classical.choice','Quot.sound'}

def rss_tree(pid):
 rows=[tuple(map(int,line.split())) for line in subprocess.check_output(['ps','-A','-o','pid=,ppid=,rss='],text=True).splitlines() if line.strip()];own={pid}
 for _ in range(len(rows)):
  more=own|{child for child,parent,rss in rows if parent in own}
  if more==own:break
  own=more
 return sum(rss for child,parent,rss in rows if child in own),rows,own

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--actual',action='store_true')
 parser.add_argument('--normal',action='store_true')
 parser.add_argument('--rss-gib',type=float,default=6)
 parser.add_argument('--time-seconds',type=float,default=300)
 args=parser.parse_args()
 manifest=json.loads((ROOT/'research/JSP404_SIX_SYMBOLIC_M0_NAT_SHARDS_MANIFEST_20261005.json').read_text())
 assert not(args.actual and args.normal)
 targets=([{'module':'Jsp000404.SixExactFloorKernelSymbolicMask000Probe','source':'Jsp000404/SixExactFloorKernelSymbolicMask000Probe.lean'}] if args.actual else manifest['shards']+[{'module':'Jsp000404.SixExactFloorKernelSymbolicMask000Integer','source':'Jsp000404/SixExactFloorKernelSymbolicMask000Integer.lean'}])
 if args.normal:
  targets=[{'module':'Jsp000404.SixExactFloorKernelSymbolicInterval','source':'Jsp000404/SixExactFloorKernelSymbolicInterval.lean'}]+targets+[{'module':'Jsp000404.SixExactFloorKernelSymbolicMask000Probe','source':'Jsp000404/SixExactFloorKernelSymbolicMask000Probe.lean'}]
  frozen=json.loads((ROOT/'research/JSP404_SIX_SYMBOLIC_MASK0_FREEZE_20261006.json').read_text())['source_hashes']
  assert len(targets)==40
  for target in targets:target['source_sha256']=frozen[target['source']]
 mode='normal' if args.normal else 'actual' if args.actual else 'nat';log_dir=ROOT/f'verification/six-symbolic-mask0-{mode}-20261005';log_dir.mkdir(exist_ok=True)
 receipt_path=(ROOT/'research/JSP404_SIX_SYMBOLIC_M0_NORMAL_LAKE_RECEIPT_20261006.json' if args.normal else ROOT/f'research/JSP404_SIX_SYMBOLIC_M0_{mode.upper()}_KERNEL_RECEIPT_20261005.json')
 receipt=json.loads(receipt_path.read_text()) if receipt_path.exists() else {'mode':mode,'status':'RUNNING','concurrency':1,'results':[]}
 prior={item['module']:item for item in receipt['results']}
 for target in targets:
  source=ROOT/target['source'];sha=hashlib.sha256(source.read_bytes()).hexdigest()
  if 'source_sha256' in target:assert sha==target['source_sha256']
  name=target['module'];artifact=ROOT/'.lake/build/lib/lean'/Path(target['source']).with_suffix('.olean')
  old=prior.get(name)
  if old and old['status']=='PASS' and old['source_sha256']==sha and artifact.exists() and hashlib.sha256(artifact.read_bytes()).hexdigest()==old['artifact_sha256']:continue
  if not args.normal and name.endswith('NatShard025') and not old:
   probe=json.loads((ROOT/'research/JSP404_SIX_SYMBOLIC_NAT_SHARD025_CAP6_PROBE_20261005.json').read_text())
   if probe['status']=='PASS' and probe['source_sha256']==sha and artifact.exists():
    raw=Path(probe['log']);output=raw.read_text();axioms=re.findall(r'depends on axioms: \[([^\]]*)\]',output)
    assert axioms and all(set(a.replace(',',' ').split()).issubset(STANDARD) for a in axioms)
    result={'module':name,'source_sha256':sha,'status':'PASS','exit_code':0,'seconds':probe['seconds'],'peak_sampled_tree_rss_kib':probe['peak_sampled_process_tree_rss_kib'],'log':str(raw),'axioms':axioms,'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest(),'reused_real_probe_receipt':True}
    receipt['results'].append(result);continue
  log_path=log_dir/f'{name.rsplit(".",1)[1]}.txt'
  command=['lake','build',name] if args.normal else ['lake','env','lean','--trust=0','-DautoImplicit=false','-o',str(artifact),str(source)]
  rss_cap=8 if args.normal and name.endswith('Mask000Probe') else args.rss_gib
  start=time.monotonic();peak=0;stop=None
  with log_path.open('w') as log:
   proc=subprocess.Popen(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
   while proc.poll() is None:
    rss,rows,own=rss_tree(proc.pid);peak=max(peak,rss)
    if rss>=rss_cap*1024**2 or time.monotonic()-start>args.time_seconds:
     stop='RSS_CAP' if rss>=rss_cap*1024**2 else 'TIME_CAP'
     leaves=[pid for pid,parent,rss in rows if pid in own and not any(pp==pid for cc,pp,rr in rows)]
     for pid in leaves:subprocess.run(['kill','-INT',str(pid)],check=False)
     break
    time.sleep(.1)
   proc.wait(timeout=20)
  output=log_path.read_text();axioms=re.findall(r'depends on axioms: \[([^\]]*)\]',output)
  ok=proc.returncode==0 and not stop and 'error:' not in output and artifact.exists() and (args.normal or axioms) and all(set(a.replace(',',' ').split()).issubset(STANDARD) for a in axioms)
  result={'module':name,'source_sha256':sha,'status':'PASS' if ok else 'NOT_PROVED','exit_code':proc.returncode,'resource_stop':stop,'rss_cap_gib':rss_cap,'seconds':time.monotonic()-start,'peak_sampled_tree_rss_kib':peak,'command':command,'log':str(log_path.relative_to(ROOT)),'log_sha256':hashlib.sha256(log_path.read_bytes()).hexdigest(),'axioms':axioms,'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest() if ok and artifact.exists() else None}
  receipt['results']=[item for item in receipt['results'] if item['module']!=name]+[result];receipt['completed']=sum(item['status']=='PASS' for item in receipt['results']);receipt['status']='RUNNING' if ok else 'NOT_PROVED';receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
  print(json.dumps({key:result[key] for key in ('module','status','seconds','peak_sampled_tree_rss_kib')}),flush=True)
  if not ok:raise RuntimeError(f'{name} not proved; own dispatch stopped')
 receipt['status']='PASS';receipt['expected_targets']=len(targets);receipt['completed']=len(targets);receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')

if __name__=='__main__':main()
