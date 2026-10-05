#!/usr/bin/env python3
"""Generate actual typed reflection transport between two orientation masks."""
from pathlib import Path
import argparse,hashlib,json
from export_six_exact_floor_kernel_20261005 import TRIPLES
ROOT=Path(__file__).resolve().parents[1]
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--proved-mask',type=int,default=567);args=ap.parse_args();mask=args.proved_mask
 perm=[TRIPLES.index(tuple(sorted(4-i for i in tri))) for tri in TRIPLES];mirror=sum(((mask>>i)&1)<<j for i,j in enumerate(perm))
 def d(i,j):return f'M.d {i} {j}'
 def tri_expr(bit,mask,chord):
  i,j,k=TRIPLES[bit];x,y,z=chord(i,j),chord(i,k),chord(j,k);lo,hi=(z,x) if mask>>bit&1 else(x,z)
  return f'{lo} + 1 ≤ {hi} ∧ {lo} < {y} ∧ {y} < {hi}'
 lines=[f'import Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}Probe','import Jsp000404.SixModelReflection','',
 '/-! Actual ModelSix reflection transport. No original-point realization is assumed. -/',
 'namespace Jsp404.SixExactFloorKernel',f'theorem symbolic_mask{mirror}_probe {{n : ℕ}} (M : SixModelCompression.ModelSix n)',
 '    (hn4 : 4 ≤ n) (hhigh : (1/2 : ℝ) ≤ M.delta)']
 for i,c in ((0,2),(1,3),(3,3),(4,2)):lines += [f'    (hdef{i} : SixModelCompression.rowDefect M {i} = {c})']
 for bit,(i,j,k) in enumerate(TRIPLES):lines += [f'    (htri{i}{j}{k} : '+tri_expr(bit,mirror,d)+')']
 lines += ['    : False := by','  let R := SixModelReflection.reflectedModel M',
 '  have hhighR : (1/2 : ℝ) ≤ R.delta := hhigh']
 for i,c in ((0,2),(1,3),(3,3),(4,2)):
  lines += [f'  have hdefR{i} : SixModelCompression.rowDefect R {i} = {c} := by',
 f'    change SixModelCompression.rowDefect (SixModelReflection.reflectedModel M) {i} = {c}',
 '    rw [SixModelReflection.reflectedModel_rowDefect]',
 f'    change SixModelCompression.rowDefect M {4-i} = {c}',f'    exact hdef{4-i}']
 for i in range(5):
  for j in range(i):lines += [f'  have hs{i}{j} : M.d {i} {j} = M.d {j} {i} := M.symm {i} {j} (by decide)']
 for bit,(i,j,k) in enumerate(TRIPLES):
  original=tuple(sorted((4-i,4-j,4-k)));a,b,c=original
  lines += [f'  have hr{i}{j}{k} : '+tri_expr(bit,mask,lambda i,j:f'R.d {i} {j}')+' := by',
            '    change '+tri_expr(bit,mask,lambda i,j:f'((n : ℝ) + 2 * M.delta - M.d {4-i} {4-j})'),
            f'    simp only [hs{4-i}{4-j}, hs{4-i}{4-k}, hs{4-j}{4-k}]',
            f'    obtain ⟨ha, hb, hc⟩ := htri{a}{b}{c}',
            '    constructor <;> try constructor','    all_goals linarith only [ha, hb, hc]']
 args=['R','hn4','hhighR']+[f'hdefR{i}' for i in (0,1,3,4)]+[f'hr{i}{j}{k}' for i,j,k in TRIPLES]
 lines += [f'  exact symbolic_mask{mask}_probe '+' '.join(args),f'\n#print axioms symbolic_mask{mirror}_probe','end Jsp404.SixExactFloorKernel']
 path=ROOT/f'Jsp000404/SixExactFloorKernelSymbolicMask{mask:03d}Reflection.lean';path.write_text('\n'.join(lines)+'\n')
 print(json.dumps({'proved_mask':mask,'transported_mask':mirror,'source':str(path.relative_to(ROOT)),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'kernel':'NOT_RUN'}))
if __name__=='__main__':main()
