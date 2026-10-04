#!/usr/bin/env python3
"""Generate ordinary Lean branching + linarith, never trusted SMT proofs.
Z3 only chooses splits and a subset of inequalities at each inconsistent
leaf. Every resulting leaf must be checked by Lean's kernel under trust=0.
"""
import itertools,json,time
from pathlib import Path
import z3
ROOT=Path(__file__).resolve().parents[1]
N=5
L=z3.Real('lam');P=z3.Real('p')
D={(i,j):z3.Real(f'd{i}{j}') for i,j in itertools.combinations(range(N),2)}
get=lambda i,j:D[tuple(sorted((i,j)))]
started=time.monotonic();stats={'nodes':0,'leaves':0,'max_depth':0}

def conjunction(atoms):return z3.And(*[v for _,v in atoms])
def run(base,pending):
    S=z3.SolverFor('QF_LRA');S.set(timeout=10000)
    for name,x in base.items():S.assert_and_track(x,z3.Bool(name))
    for name,info in pending.items():S.assert_and_track(info['expr'],z3.Bool(name))
    ans=S.check()
    if ans==z3.unknown:raise RuntimeError(S.reason_unknown())
    return ans,[str(x) for x in S.unsat_core()] if ans==z3.unsat else []

def triangle(i,j,k):
    x,y,z=get(i,j),get(i,k),get(j,k)
    prefix=f'htr{i}{j}{k}'
    names=[prefix+t for t in 'abcde']
    arms=[[x+L<=z,x<y,y<z,y-x<=P-L,z-y<=P-L],[z+L<=x,z<y,y<x,y-z<=P-L,x-y<=P-L]]
    return {'kind':'tri','ijk':(i,j,k),'names':names,'arms':arms,'expr':z3.Or(*[z3.And(*a) for a in arms])}

def window(i,j,k):
    a,b=get(i,j),get(i,k);prefix=f'hw{i}{j}{k}';names=[prefix+'a',prefix+'b']
    arms=[[b<a,b+P-a<=P-2*L],[a<=b,b-a<=P-2*L]]
    return {'kind':'win','ijk':(i,j,k),'names':names,'arms':arms,'expr':z3.Or(*[z3.And(*a) for a in arms])}

def cut(i):
    choices={j:[window(i,j,k) for k in range(N) if k not in (i,j)] for j in range(N) if j!=i}
    return {'kind':'cut','i':i,'choices':choices,'expr':z3.Or(*[z3.And(*[w['expr'] for w in ws]) for ws in choices.values()])}

def indent(lines,amount=2):return[' '*amount+x for x in lines]

def tree(base,pending,depth=0):
    stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
    ans,core=run(base,{})
    if ans==z3.unsat:
        stats['leaves']+=1
        return ['linarith only ['+', '.join(core)+']']
    ans,core=run(base,pending)
    if ans!=z3.unsat:raise RuntimeError('Unexpected satisfiable branch')
    candidates=[x for x in core if x in pending]
    # Prefer an available modular choice, then a binary triangle split;
    # cut witnesses each introduce at most three modular choices.
    candidates.sort(key=lambda x:({'win':0,'tri':1,'cut':2}[pending[x]['kind']],x))
    chosen=candidates[0];info=pending[chosen];remaining={k:v for k,v in pending.items() if k!=chosen}
    kind=info['kind']
    if kind in ('tri','win'):
        names=info['names'];pat='⟨'+', '.join(names)+'⟩'
        if kind=='tri':
            i,j,k=info['ijk'];head=f'rcases m.htr {i} {j} {k} (by decide) (by decide) with'
        else:
            i,j,k=info['ijk'];head=f'rcases hwindow{i}{j}{k} with'
        lines=[head,'  '+pat+' | '+pat]
        for arm in info['arms']:
            b=dict(base);b.update(zip(names,arm))
            lines+=['·']+indent(tree(b,remaining,depth+1))
        return lines
    i=info['i'];lines=[f'obtain ⟨j{i}, hj{i}, hcut{i}⟩ := hpos {i} (by decide)',f'fin_cases j{i}']
    for j in range(N):
        lines+=['·']
        if j==i:lines+=['  exact hj'+str(i)+' rfl'];continue
        branch=[];p=dict(remaining)
        for w in info['choices'][j]:
            _,_,k=w['ijk'];used=', '.join(f'hcanon{i}{other}' for other in (j,k) if i>other);branch += [f'have hraw{i}{j}{k} := hcut{i} {k} (by decide)',f'change (if m.d {i} {k} < m.d {i} {j} then m.d {i} {k}+p-m.d {i} {j} else m.d {i} {k}-m.d {i} {j}) ≤ p-2*lam at hraw{i}{j}{k}']
            if used:branch += [f'simp only [{used}] at hraw{i}{j}{k}']
            branch += [f'have hwindow{i}{j}{k} := window_cases hraw{i}{j}{k}']
            p[f'window{i}{j}{k}']=w
        branch+=tree(base,p,depth+1);lines+=indent(branch)
    return lines

header='''import Jsp000404.MixedStarExclusion

/-! Ordinary finite LOW terminal with complete triangle caps. The generator
uses a diagnostic solely to select branches; every leaf is ordinary
`linarith`, checked by Lean. No SMT result is trusted by this module. -/

namespace Jsp404.NoSatFiveTerminal

structure FiveModel (lam p : ℝ) where
  hlam : 0 < lam
  hp : 3*lam ≤ p ∧ 2*p < 7*lam
  d : Fin 5 → Fin 5 → ℝ
  hsymm : ∀ i j, d i j = d j i
  hrange : ∀ i j, i ≠ j → 0 ≤ d i j ∧ d i j < p
  htr : ∀ i j k : Fin 5, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k ∧
      d i k-d i j ≤ p-lam ∧ d j k-d i k ≤ p-lam) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j ∧
      d i k-d j k ≤ p-lam ∧ d i j-d i k ≤ p-lam)

lemma window_cases {a b p lam : ℝ}
    (h : (if b < a then b+p-a else b-a) ≤ p-2*lam) :
    (b<a ∧ b+p-a ≤ p-2*lam) ∨ (a≤b ∧ b-a ≤ p-2*lam) := by
  by_cases hb : b<a
  · exact Or.inl ⟨hb, by simpa [hb] using h⟩
  · exact Or.inr ⟨le_of_not_gt hb, by simpa [hb] using h⟩

'''
base={'hlam':L>0,'hp0':3*L<=P,'hp1':2*P<7*L}
setup=['have hlam := m.hlam','have hp0 := m.hp.1','have hp1 := m.hp.2']
for (i,j),x in D.items():
    setup += [f'obtain ⟨hd{i}{j}a, hd{i}{j}b⟩ := m.hrange {i} {j} (by decide)']
    base[f'hd{i}{j}a']=x>=0;base[f'hd{i}{j}b']=x<P
# Canonicalize only the ten backward numeric pairs; no general rewrite loop.
canon_names=', '.join(f'hcanon{j}{i}' for i,j in D)
for i,j in D:setup += [f'have hcanon{j}{i} := m.hsymm {j} {i}']
source=[header]
for q in range(N):
    print('start q',q,'nodes',stats['nodes'],flush=True)
    th=f'''set_option maxHeartbeats 16000000 in
private theorem five_model_exclusion_{q} {{lam p : ℝ}} (m : FiveModel lam p)
    (hpos : ∀ i : Fin 5, i ≠ {q} → ∃ j : Fin 5, j ≠ i ∧
      ∀ k : Fin 5, k ≠ i →
      (if m.d i k < m.d i j then m.d i k+p-m.d i j else m.d i k-m.d i j) ≤ p-2*lam) :
    False := by
'''
    pending={f'tri{i}{j}{k}':triangle(i,j,k) for i,j,k in itertools.combinations(range(N),3)}
    pending.update({f'cut{i}':cut(i) for i in range(N) if i!=q})
    proof=setup+tree(base,pending)
    source += [th+'\n'.join(indent(proof))+'\n\n']
    print('finish q',q,'stats',stats,flush=True)
source+=['''theorem five_model_impossible {lam p : ℝ} (m : FiveModel lam p) (q : Fin 5)
    (hpos : ∀ i : Fin 5, i ≠ q → ∃ j : Fin 5, j ≠ i ∧
      ∀ k : Fin 5, k ≠ i →
      (if m.d i k < m.d i j then m.d i k+p-m.d i j else m.d i k-m.d i j) ≤ p-2*lam) :
    False := by
  fin_cases q
''']
for q in range(N):source+= [f'  · exact five_model_exclusion_{q} m hpos\n']
source+=['\n#print axioms five_model_impossible\nend Jsp404.NoSatFiveTerminal\n']
(ROOT/'Jsp000404/NoSatFiveTerminal.lean').write_text(''.join(source))
stats['elapsed_seconds']=round(time.monotonic()-started,3)
(ROOT/'research/JSP404_NOSAT_FIVE_TERMINAL_GENERATOR_20261004.json').write_text(json.dumps(stats,indent=2)+'\n')
print(stats,flush=True)
