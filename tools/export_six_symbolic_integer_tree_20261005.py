#!/usr/bin/env python3
"""Export complete adaptive Nat-min branch trees as ordinary Omega shards.

All SMT branch/core data are untrusted until each Lean source is checked.
"""
from pathlib import Path
import json,sys,hashlib
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import probe_six_symbolic_cycles_20261005 as p
p.NAMES.extend(f'u{i}{k}' for i in p.DEFECTS for k in range(5));p.INDEX.update({n:i for i,n in enumerate(p.NAMES)})
report=json.loads((ROOT/'research/JSP404_SIX_SYMBOLIC_CYCLES_M0_BUNBOUNDED_MIN_20261005.json').read_text())
data=json.loads((ROOT/'research/JSP404_SIX_SYMBOLIC_M0_INTEGER_TREE_PRUNED_20261005.json').read_text())
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
  return [pre+f'exact symbolic_mask0_integer_shard{index:03d} '+' '.join(args)]
 i,k=node['i'],node['k'];name=f'hcase{i}{k}';left=f'hcase{i}{k}0';right=f'hcase{i}{k}1'
 lines=[pre+f'rcases {name} with ⟨{left}a, {left}b⟩ | ⟨{right}a, {right}b⟩']
 for arm,child in enumerate(node['children']):
  facts=[(f'hcase{i}{k}{arm}a',f's{i}{k} = 0' if arm==0 else f'1 ≤ s{i}{k}'),(f'hcase{i}{k}{arm}b',f'u{i}{k} = {arm}')]
  lines += [pre+'·']+render(child,prefix+facts,[n for n in remaining if n!=name],indent+2)
 return lines
receipts=[]
for index,(node,prefix) in enumerate(shards):
 module=f'SixExactFloorKernelSymbolicMask000NatShard{index:03d}';theorem=f'symbolic_mask0_integer_shard{index:03d}'
 source=['import Mathlib.Data.Nat.Basic','import Lean.Elab.Tactic.Omega','',
 'namespace Jsp404.SixExactFloorKernel','set_option maxHeartbeats 16000000 in',
 f'theorem {theorem} ('+' '.join(p.NAMES)+' : ℕ)']
 source += [f'    ({n} : {ty})' for n,ty in base+cases+prefix]
 source += ['    : False := by']+render(node,prefix,case_names)
 source += [f'\n#print axioms {theorem}','end Jsp404.SixExactFloorKernel']
 text='\n'.join(source)+'\n';path=ROOT/'Jsp000404'/f'{module}.lean';path.write_text(text)
 receipts.append({'module':'Jsp000404.'+module,'theorem':'Jsp404.SixExactFloorKernel.'+theorem,'source':str(path.relative_to(ROOT)),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'leaves':leaf_count(node),'lines':len(text.splitlines()),'bytes':len(text.encode()),'prefix':prefix,'kernel':'NOT_RUN'})
source=[f'import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard{i:03d}' for i in range(len(shards))]
source += ['','namespace Jsp404.SixExactFloorKernel',
 'private theorem min_score_cases (s u : ℕ) (hmin : u = min s 1) :',
 '    (s = 0 ∧ u = 0) ∨ (1 ≤ s ∧ u = 1) := by omega','',
 'set_option maxHeartbeats 16000000 in','theorem symbolic_mask0_integer_closure ('+' '.join(p.NAMES)+' : ℕ)']
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
  return [pre+f'exact symbolic_mask0_integer_shard{index:03d} '+' '.join(args)]
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
source += ['\n#print axioms symbolic_mask0_integer_closure','end Jsp404.SixExactFloorKernel']
path=ROOT/'Jsp000404/SixExactFloorKernelSymbolicMask000Integer.lean';path.write_text('\n'.join(source)+'\n')
manifest={'status':'SOURCE_ONLY','shards':receipts,'top_tree':top,'largest':max(receipts,key=lambda r:r['leaves']),'total_leaves':sum(r['leaves'] for r in receipts),'kernel':'NOT_RUN'}
(ROOT/'research/JSP404_SIX_SYMBOLIC_M0_NAT_SHARDS_MANIFEST_20261005.json').write_text(json.dumps(manifest,indent=2)+'\n')
print({'shards':len(shards),'leaves':manifest['total_leaves'],'lines':sum(r['lines'] for r in receipts),'bytes':sum(r['bytes'] for r in receipts),'largest':manifest['largest']['module']})
