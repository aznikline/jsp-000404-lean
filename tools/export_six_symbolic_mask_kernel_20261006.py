#!/usr/bin/env python3
"""Export complete adaptive Nat-min branch trees as ordinary Omega shards.

All SMT branch/core data are untrusted until each Lean source is checked.
"""
from pathlib import Path
import json,sys,hashlib,argparse
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import probe_six_symbolic_cycles_20261005 as p
p.NAMES.extend(f'u{i}{k}' for i in p.DEFECTS for k in range(5));p.INDEX.update({n:i for i,n in enumerate(p.NAMES)})
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--mask',type=int,default=567)
args=ap.parse_args();mask=args.mask
assert mask!=0, 'The frozen mask0 source is never rewritten by this exporter.'
public_report=ROOT/f'research/JSP404_SIX_SYMBOLIC_CYCLES_M{mask}_BUNBOUNDED_MIN_20261005.json'
public_tree=ROOT/f'research/JSP404_SIX_SYMBOLIC_M{mask}_INTEGER_TREE_PRUNED_20261006.json'
if public_report.exists() and public_tree.exists():
 report=json.loads(public_report.read_text());data=json.loads(public_tree.read_text())
else:
 cases=json.loads((ROOT/'research/JSP404_SIX_SYMBOLIC_REPS_DIAGNOSTIC_20261006.json').read_text())['results']
 case=next(c for c in cases if c['mask']==mask)
 report=json.loads((ROOT/case['private_diagnostic_path']).read_text())
 trees=json.loads((ROOT/'research/JSP404_SIX_SYMBOLIC_REPS_TREE_SIZES_20261006.json').read_text())['results']
 tree_case=next(c for c in trees if c['mask']==mask)
 assert tree_case['status']=='COMPLETE_TREE' and tree_case['fingerprint_sha256']==case['fingerprint_sha256']
 data=json.loads((ROOT/tree_case['private_tree_path']).read_text())
 assert hashlib.sha256((ROOT/case['private_diagnostic_path']).read_bytes()).hexdigest()==case['private_diagnostic_sha256']
 assert hashlib.sha256((ROOT/tree_case['private_tree_path']).read_bytes()).hexdigest()==tree_case['private_tree_sha256']
# Prune only a split whose complete child proof does not depend on its arm facts.
def prune(node):
 if 'core' in node:return node,set(node['core'])
 i,k=node['i'],node['k'];children=[prune(child) for child in node['children']]
 arms=[{f'hcase{i}{k}{a}{s}' for s in 'ab'} for a in range(2)]
 for a,(child,deps) in enumerate(children):
  if not(deps&arms[a]):return child,deps
 return {'i':i,'k':k,'children':[child for child,deps in children]},set().union(*(deps-arm for (child,deps),arm in zip(children,arms)))
data['tree']=prune(data['tree'])[0]
selected=data['selected_cut_names'];lookup={cut['name']:cut for cut in report['cuts']}
root=data['tree'];pairs=[(i,k) for i in p.DEFECTS for k in range(5)]
def poly(coeffs,c):
 entries=[name if n==1 else f'{n} * {name}' for name,n in coeffs]
 if c:entries.append(str(c))
 return '('+' + '.join(entries or ['0'])+')'
base=[('hn4','4 ≤ n')]
for i,c in p.DEFECTS.items():
 ss=[f's{i}{k}' for k in range(5)];ns=ss[-1]
 for s in reversed(ss[:-1]):ns=f'{s} + ({ns})'
 base.append((f'hsum_nat{i}',f'({ns}) + {c} = n'))
for name in selected:
 cut=lookup[name];a=cut['A'];pos=poly([(n,c) for n,c in a['coefficients'].items() if c>0],max(a['constant'],0));neg=poly([(n,-c) for n,c in a['coefficients'].items() if c<0],max(-a['constant'],0))
 base.append((name,f'{neg}'+(' + 1' if cut['threshold'] else '')+f' ≤ {pos}'))
for i,k in pairs:base += [(f'hu{i}{k}b',f'u{i}{k} ≤ 1'),(f'hu{i}{k}c',f'u{i}{k} ≤ s{i}{k}')]
cases=[(f'hcase{i}{k}',f'(s{i}{k} = 0 ∧ u{i}{k} = 0) ∨ (1 ≤ s{i}{k} ∧ u{i}{k} = 1)') for i,k in pairs]
base_names=[n for n,_ in base];case_names=[n for n,_ in cases]
def leaf_count(node):return 1 if 'core' in node else sum(leaf_count(c) for c in node['children'])
shards=[]
def partition(node,prefix):
 if leaf_count(node)<=300:
  index=len(shards);shards.append((node,prefix));return {'shard':index}
 i,k=node['i'],node['k'];children=[]
 for arm,child in enumerate(node['children']):
  facts=[(f'hcase{i}{k}{arm}a',f's{i}{k} = 0' if arm==0 else f'1 ≤ s{i}{k}'),(f'hcase{i}{k}{arm}b',f'u{i}{k} = {arm}')]
  children.append(partition(child,prefix+facts))
 return {'i':i,'k':k,'children':children}
top=partition(root,[])
def render(node,prefix,remaining,indent=2):
 pre=' '*indent
 if 'core' in node:
  keep=set(node['core']);local=[n for n,_ in prefix]
  disposable=[n for n in base_names+local+remaining if n not in keep]
  # Nat nonnegativity is supplied by the variable types, not unproved fields.
  lines=[pre+'clear '+ ' '.join(disposable)] if disposable else []
  return lines+[pre+'omega']
 if 'shard' in node:
  index=node['shard'];args=p.NAMES+base_names+case_names+[n for n,_ in prefix]
  return [pre+f'exact symbolic_mask{mask}_integer_shard{index:03d} '+' '.join(args)]
 i,k=node['i'],node['k'];name=f'hcase{i}{k}';left=f'hcase{i}{k}0';right=f'hcase{i}{k}1'
 lines=[pre+f'rcases {name} with ⟨{left}a, {left}b⟩ | ⟨{right}a, {right}b⟩']
 for arm,child in enumerate(node['children']):
  facts=[(f'hcase{i}{k}{arm}a',f's{i}{k} = 0' if arm==0 else f'1 ≤ s{i}{k}'),(f'hcase{i}{k}{arm}b',f'u{i}{k} = {arm}')]
  lines += [pre+'·']+render(child,prefix+facts,[n for n in remaining if n!=name],indent+2)
 return lines
receipts=[]
for index,(node,prefix) in enumerate(shards):
 module=f'SixExactFloorKernelSymbolicMask{mask:03d}NatShard{index:03d}';theorem=f'symbolic_mask{mask}_integer_shard{index:03d}'
 source=['import Mathlib.Data.Nat.Basic','import Lean.Elab.Tactic.Omega','',
 'namespace Jsp404.SixExactFloorKernel','set_option maxHeartbeats 16000000 in',
 f'theorem {theorem} ('+' '.join(p.NAMES)+' : ℕ)']
 source += [f'    ({n} : {ty})' for n,ty in base+cases+prefix]
 source += ['    : False := by']+render(node,prefix,case_names)
 source += [f'\n#print axioms {theorem}','end Jsp404.SixExactFloorKernel']
 text='\n'.join(source)+'\n';path=ROOT/'Jsp000404'/f'{module}.lean';path.write_text(text)
 receipts.append({'module':'Jsp000404.'+module,'theorem':'Jsp404.SixExactFloorKernel.'+theorem,'source':str(path.relative_to(ROOT)),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'leaves':leaf_count(node),'lines':len(text.splitlines()),'bytes':len(text.encode()),'prefix':prefix,'kernel':'NOT_RUN'})
source=[f'import Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}NatShard{i:03d}' for i in range(len(shards))]
source += ['','namespace Jsp404.SixExactFloorKernel',
 'private theorem min_score_cases (s u : ℕ) (hmin : u = min s 1) :',
 '    (s = 0 ∧ u = 0) ∨ (1 ≤ s ∧ u = 1) := by omega','',
 'set_option maxHeartbeats 16000000 in',f'theorem symbolic_mask{mask}_integer_closure ('+' '.join(p.NAMES)+' : ℕ)']
source += [f'    ({n} : {ty})' for n,ty in base if not n.startswith('hu')]
source += [f'    (hmin{i}{k} : u{i}{k} = min s{i}{k} 1)' for i,k in pairs]
source += ['    : False := by']
for i,k in pairs:
 source += [f'  have hu{i}{k}b : u{i}{k} ≤ 1 := by rw [hmin{i}{k}]; exact Nat.min_le_right _ _',
 f'  have hu{i}{k}c : u{i}{k} ≤ s{i}{k} := by rw [hmin{i}{k}]; exact Nat.min_le_left _ _',
 f'  have hcase{i}{k} := min_score_cases s{i}{k} u{i}{k} hmin{i}{k}']
source += ['  clear '+' '.join(f'hmin{i}{k}' for i,k in pairs)]
# At wrapper split points keep untouched case hypotheses for all shard calls.
def wrapper(node,prefix,indent=2):
 pre=' '*indent
 if 'shard' in node:
  index=node['shard'];args=p.NAMES+base_names+case_names+[n for n,_ in prefix]
  return [pre+f'exact symbolic_mask{mask}_integer_shard{index:03d} '+' '.join(args)]
 i,k=node['i'],node['k'];case=f'hcase{i}{k}'
 lines=[pre+f'rcases {case} with ⟨hcase{i}{k}0a, hcase{i}{k}0b⟩ | ⟨hcase{i}{k}1a, hcase{i}{k}1b⟩']
 # Preserve original case disjunction explicitly; shard signatures use all cases.
 for arm,child in enumerate(node['children']):
  facts=[(f'hcase{i}{k}{arm}a',f's{i}{k} = 0' if arm==0 else f'1 ≤ s{i}{k}'),(f'hcase{i}{k}{arm}b',f'u{i}{k} = {arm}')]
  conj=f'⟨hcase{i}{k}{arm}a, hcase{i}{k}{arm}b⟩'
  lines += [pre+'·',pre+f'  have {case} : (s{i}{k} = 0 ∧ u{i}{k} = 0) ∨ (1 ≤ s{i}{k} ∧ u{i}{k} = 1) := Or.in'+('l' if arm==0 else 'r')+f' {conj}']
  lines += wrapper(child,prefix+facts,indent+2)
 return lines
source += wrapper(top,[])
source += [f'\n#print axioms symbolic_mask{mask}_integer_closure','end Jsp404.SixExactFloorKernel']
path=ROOT/f'Jsp000404/SixExactFloorKernelSymbolicMask{mask:03d}Integer.lean';path.write_text('\n'.join(source)+'\n')
manifest={'status':'SOURCE_ONLY','shards':receipts,'top_tree':top,'largest':max(receipts,key=lambda r:r['leaves']),'total_leaves':sum(r['leaves'] for r in receipts),'kernel':'NOT_RUN'}
(ROOT/f'research/JSP404_SIX_SYMBOLIC_M{mask}_NAT_SHARDS_MANIFEST_20261006.json').write_text(json.dumps(manifest,indent=2)+'\n')
print({'shards':len(shards),'leaves':manifest['total_leaves'],'lines':sum(r['lines'] for r in receipts),'bytes':sum(r['bytes'] for r in receipts),'largest':manifest['largest']['module']})

# Save the selected symbolic premise data for the actual ModelSix replay.
(ROOT/f'research/JSP404_SIX_SYMBOLIC_CYCLES_M{mask}_BUNBOUNDED_MIN_20261005.json').write_text(json.dumps(report,indent=2)+'\n')
(ROOT/f'research/JSP404_SIX_SYMBOLIC_CYCLES_M{mask}_MIN_CORE_20261005.json').write_text(json.dumps({'selected_cut_names':selected,'kernel':'NOT_RUN'},indent=2)+'\n')
p.emit_min_probe(mask)
