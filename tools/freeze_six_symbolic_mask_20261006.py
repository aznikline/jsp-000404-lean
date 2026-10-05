#!/usr/bin/env python3
"""Freeze verified fixed-orientation samples and their genuine artifacts."""
from pathlib import Path
import argparse,json,hashlib
ROOT=Path(__file__).resolve().parents[1]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--mask',type=int,required=True);args=ap.parse_args();mask=args.mask;assert mask not in (0,567)
 path=ROOT/f'research/JSP404_SIX_SYMBOLIC_MASK{mask}_SOURCE_FREEZE_20261006.json';f=json.loads(path.read_text());receipts={}
 for stage in ('NAT','ACTUAL','REFLECTION','NORMAL'):
  p=ROOT/f'research/JSP404_SIX_SYMBOLIC_M{mask}_{stage}_RECEIPT_20261006.json';r=json.loads(p.read_text());assert r['status']=='PASS';receipts[stage]=(p,r)
 for r in receipts['NORMAL'][1]['results']:
  source=ROOT/r['source'];assert sha(source)==r['source_sha256']==f['source_hashes'][r['source']]
  artifact=ROOT/'.lake/build/lib/lean'/Path(r['source']).with_suffix('.olean');assert sha(artifact)==r['artifact_sha256'] and r['exit_code']==0
 treecases=json.loads((ROOT/'research/JSP404_SIX_SYMBOLIC_REPS_TREE_SIZES_20261006.json').read_text())['results'];case=next(c for c in treecases if c['mask']==mask);data=json.loads((ROOT/case['private_tree_path']).read_text())
 def prune(n):
  if 'core' in n:return n,set(n['core'])
  i,k=n['i'],n['k'];cs=[prune(c) for c in n['children']];arms=[{f'hcase{i}{k}{a}{s}' for s in 'ab'} for a in range(2)]
  for a,(c,dep) in enumerate(cs):
   if not(dep&arms[a]):return c,dep
  return {'i':i,'k':k,'children':[c for c,dep in cs]},set().union(*(dep-arm for (c,dep),arm in zip(cs,arms)))
 data['tree']=prune(data['tree'])[0];tree=ROOT/f'research/JSP404_SIX_SYMBOLIC_M{mask}_INTEGER_TREE_PRUNED_20261006.json';tree.write_text(json.dumps(data,indent=2)+'\n')
 permutation=[9,8,5,7,4,2,6,3,1,0];mirror=sum(((mask>>i)&1)<<j for i,j in enumerate(permutation))
 f.update({'kernel':'PASS','normal_lake':'PASS','reflection_mask':mirror,'covered_new_directions':[mask] if mirror==mask else [mask,mirror],'strict_sources':len(f['source_hashes']),'normal_sources':len(f['source_hashes']),'scope':'Only fixed orientation and its actual reflected orientation, all natural n>=4 HIGH ModelSix, defects(2,3,*,3,2) and all ten explicit triangle hypotheses. Not all31/all62/full JSP.','public_imports':[f'Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}Probe',f'Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}Reflection'],'public_theorems':[f'Jsp404.SixExactFloorKernel.symbolic_mask{mask}_probe',f'Jsp404.SixExactFloorKernel.symbolic_mask{mirror}_probe' if mirror!=mask else f'Jsp404.SixExactFloorKernel.symbolic_mask{mirror}_reflection_transport'],'receipts':{stage:{'path':str(p.relative_to(ROOT)),'sha256':sha(p)} for stage,(p,r) in receipts.items()},'normal_seconds':sum(x['seconds'] for x in receipts['NORMAL'][1]['results']),'normal_sampled_peak_tree_rss_kib':max(x['sampled_peak_tree_rss_kib'] for x in receipts['NORMAL'][1]['results'])})
 f['publish_files']=list(f['source_hashes'])+['tools/export_six_symbolic_mask_kernel_20261006.py','tools/export_six_symbolic_reflection_20261006.py','tools/check_six_symbolic_mask_kernel_20261006.py','tools/freeze_six_symbolic_mask_20261006.py']+(['tools/export_six_symbolic_cohort_reflection_20261006.py'] if mirror==mask else [])+[str(path.relative_to(ROOT)),str(tree.relative_to(ROOT)),f'research/JSP404_SIX_SYMBOLIC_CYCLES_M{mask}_BUNBOUNDED_MIN_20261005.json',f'research/JSP404_SIX_SYMBOLIC_CYCLES_M{mask}_MIN_CORE_20261005.json',f'research/JSP404_SIX_SYMBOLIC_M{mask}_NAT_SHARDS_MANIFEST_20261006.json']+[str(p.relative_to(ROOT)) for p,r in receipts.values()]+[f'verification/six-symbolic-mask{mask}-{stage}-20261006' for stage in ('nat','actual','reflection','normal')]
 f['generator_hashes']={p:sha(ROOT/p) for p in f['publish_files'] if p.startswith('tools/')};path.write_text(json.dumps(f,indent=2)+'\n');print(json.dumps({'mask':mask,'mirror':mirror,'strict_and_normal':'PASS','sources':len(f['source_hashes']),'normal_seconds':f['normal_seconds'],'peak_gib':f['normal_sampled_peak_tree_rss_kib']/1024**2,'freeze':str(path.relative_to(ROOT))}))
if __name__=='__main__':main()
