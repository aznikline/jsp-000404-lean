#!/usr/bin/env python3
"""Generate ordinary Lean proofs for the fixed n=4 four-row necessary model.
SMT chooses branches/cores only.  Every leaf is untrusted until Lean checks it.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import z3

ROOT = Path(__file__).resolve().parents[1]
EDGES = list(itertools.combinations(range(5), 2))
TRIPLES = list(itertools.combinations(range(5), 3))
DEFECTS = {0: 2, 1: 3, 3: 3, 4: 2}
DE = z3.Real('delta')
T = [z3.Real(f't{i}') for i in range(5)]
D = {e: z3.Real(f'd{e[0]}{e[1]}') for e in EDGES}
BASE = {'hdelta0': DE >= z3.RealVal('1/2'), 'hdelta1': DE < 1}
for i in range(5):
    BASE[f'ht{i}a'], BASE[f'ht{i}b'] = T[i] >= 0, T[i] <= DE
    if i < 4:
        BASE[f'ht{i}{i+1}'] = T[i] < T[i+1]
for (i,j),d in D.items():
    BASE[f'hc{i}{j}a'], BASE[f'hc{i}{j}b'] = T[i]+1 <= d, d <= 3+DE+T[j]


def triangle(i,j,k):
    x,y,z = D[i,j],D[i,k],D[j,k]
    return {'kind':'tri', 'ijk':(i,j,k), 'names':[f'htr{i}{j}{k}'+s for s in 'abc'],
            'arms':[[x+1<=z,x<y,y<z],[z+1<=x,z<y,y<x]]}


TRI = {f'tri{i}{j}{k}':triangle(i,j,k) for i,j,k in TRIPLES}


def row_orders(mask):
    closure = {e:set() for e in EDGES}
    for bit,(i,j,k) in enumerate(TRIPLES):
        x,y,z=(i,j),(i,k),(j,k)
        a,b,c=(z,y,x) if mask>>bit&1 else (x,y,z)
        closure[a].add(b);closure[b].add(c)
    for _ in range(10):
        closure={a:set(bs).union(*(closure[b] for b in bs)) for a,bs in closure.items()}
    rows={}
    for i in DEFECTS:
        es=[tuple(sorted((i,j))) for j in range(5) if i!=j];original=tuple(es)
        es.sort(key=lambda e:sum(e in closure[f] for f in original))
        assert all(es[b] in closure[es[a]] for a in range(4) for b in range(a+1,4))
        rows[i]=es
    return rows


def budgets(rows):
    result={};maxima={}
    for i,c in DEFECTS.items():
        xs=[D[e] for e in rows[i]]
        gs=[xs[0]-T[i]]+[xs[k+1]-xs[k] for k in range(3)]+[T[i]+4+DE-xs[3]]
        for k,g in enumerate(gs):maxima[f'hmax{i}{k}']=g<6-c
        if c==2:
            choices=[[g>=3] for g in gs]+[[gs[a]>=2,gs[b]>=2] for a,b in itertools.combinations(range(5),2)]
        else:
            choices=[[gs[k]>=2]+[g<2 for j,g in enumerate(gs) if j!=k] for k in range(5)]
        result[f'row{i}']={'kind':'row','i':i,'c':c,'gaps':gs,'arms':choices}
    return maxima,result


class Generator:
    def __init__(self, wall, nodes):
        self.started=time.monotonic();self.wall=wall;self.limit=nodes
        self.stats={'nodes':0,'linarith_leaves':0,'triangle_nodes':0,'budget_nodes':0,'profiles':0}
        self.profiles={}

    def run(self,base,pending):
        solver=z3.SolverFor('QF_LRA');solver.set(timeout=2000,random_seed=0)
        for name,value in base.items():solver.assert_and_track(value,z3.Bool(name))
        for name,info in pending.items():
            solver.assert_and_track(z3.Or(*[z3.And(*a) for a in info['arms']]),z3.Bool(name))
        status=solver.check()
        if status==z3.unknown:raise RuntimeError(solver.reason_unknown())
        return status,([str(x) for x in solver.unsat_core()] if status==z3.unsat else [])

    def tree(self,base,pending,mask=0,phase='tri'):
        if time.monotonic()-self.started>self.wall or self.stats['nodes']>=self.limit:
            raise TimeoutError('authorized generation size/time budget exhausted')
        self.stats['nodes']+=1
        status,core=self.run(base,{})
        if status==z3.unsat:
            self.stats['linarith_leaves']+=1
            return {'core':core}
        if not pending:
            if phase=='row':raise RuntimeError('SAT simplified real n4 model')
            rows=row_orders(mask);maxima,row_pending=budgets(rows)
            self.stats['profiles']+=1
            tree=self.tree({**base,**maxima},row_pending,mask,'row')
            self.profiles[mask]=rows
            return {'profile':mask,'child':tree}
        status,core=self.run(base,pending)
        if status!=z3.unsat and phase=='row':raise RuntimeError('SAT simplified row model')
        candidates=[name for name in core if name in pending] if status==z3.unsat else list(pending)
        if phase=='tri':
            chosen=min(candidates,key=lambda name:TRIPLES.index(pending[name]['ijk']))
            self.stats['triangle_nodes']+=1
        else:
            def alive_count(name):
                return sum(self.run({**base,'__trial'+str(k):z3.And(*arm)}, {})[0]!=z3.unsat
                           for k,arm in enumerate(pending[name]['arms']))
            chosen=min(candidates,key=lambda name:(alive_count(name),name))
            self.stats['budget_nodes']+=1
        info=pending[chosen];remaining={n:v for n,v in pending.items() if n!=chosen};children=[]
        for k,arm in enumerate(info['arms']):
            if phase=='tri':
                names=info['names'];next_mask=mask|(k<<TRIPLES.index(info['ijk']))
            else:
                i=info['i'];names=[f'hb{i}{s}' for s in range(len(arm))];next_mask=mask
            children.append(self.tree({**base,**dict(zip(names,arm))},remaining,next_mask,phase))
        return {'kind':info['kind'],'info':info,'children':children}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wall-seconds',type=float,default=58)
    parser.add_argument('--max-nodes',type=int,default=12000)
    parser.add_argument('--emit-cached',action='store_true')
    args=parser.parse_args();gen=Generator(args.wall_seconds,args.max_nodes)
    if args.emit_cached:
        import pickle
        with open('/tmp/jsp404_n4_strong_tree_20261005.pkl','rb') as source:cached=pickle.load(source)
        source=emit(cached['tree'],cached['profiles'])
        path=ROOT/'Jsp000404/N4StrongFourRowTerminal.lean';path.write_text(source)
        report={**cached['stats'],'lean_lines':len(source.splitlines()),'lean_bytes':len(source.encode()),
                'kernel_status':'NOT_RUN','source':str(path)}
        (ROOT/'research/JSP404_N4_STRONG_CERTIFICATE_SIZE_20261005.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report));return
    try:
        tree=gen.tree(BASE,TRI);status='COMPLETE_TREE'
    except (TimeoutError,RuntimeError) as exc:
        tree=None;status=str(exc)
    report={**gen.stats,'generation_status':status,'seconds':time.monotonic()-gen.started,
            'kernel_status':'NOT_RUN','no_solver_answer_trusted':True}
    (ROOT/'research/JSP404_N4_STRONG_CERTIFICATE_SIZE_20261005.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)
    if tree is not None:
        import pickle
        def clean(node):
            if 'core' in node:return node
            if 'profile' in node:return {'profile':node['profile'],'child':clean(node['child'])}
            info={k:v for k,v in node['info'].items() if k not in ('arms','gaps')}
            return {'kind':node['kind'],'info':info,'children':[clean(c) for c in node['children']]}
        with open('/tmp/jsp404_n4_strong_tree_20261005.pkl','wb') as output:
            pickle.dump({'tree':clean(tree),'profiles':gen.profiles,'stats':report},output)


def emit(tree,profiles):
    import export_four_row_certificate_20261004 as old
    def chord(edge):return f'M.d {edge[0]} {edge[1]}'
    def rlist(edges):return '['+', '.join(chord(e) for e in edges)+']'
    def gap_strings(i,edges):
        xs=[chord(e) for e in edges]
        return [f'({xs[0]} - M.theta {i})']+[f'({xs[k+1]} - {xs[k]})' for k in range(3)]+[f'(M.theta {i} + (4 + M.delta) - {xs[3]})']
    def sublist_term(values,selected):
        term='List.Sublist.slnil'
        for k in reversed(range(5)):
            ctor='cons_cons' if k in selected else 'cons'
            term=f'(List.Sublist.{ctor} ({values[k]}) {term})'
        return term
    def setup_profile(mask,indent):
        lines=[];pre=' '*indent;rows=profiles[mask]
        for i,c in DEFECTS.items():
            es=rows[i];raw=[tuple(sorted((i,j))) for j in range(5) if j!=i];values=gap_strings(i,es)
            lines += [pre+f'have hsort{i} : ({rlist(es)} : List ℝ).Pairwise (· ≤ ·) := by',
                      pre+'  simp [List.pairwise_cons]',pre+'  repeat\' apply And.intro',pre+'  all_goals linarith']
            lines += [pre+f'have hp{i} := M.row_perm {i}']
            syms=[]
            for j in range(i):
                syms.append(f'hs{i}{j}');lines.append(pre+f'have hs{i}{j} : M.d {i} {j} = M.d {j} {i} := M.symm {i} {j} (by decide)')
            lines += [pre+f'have he{i} : (((List.finRange 5).erase ({i} : Fin 5)).map (M.d {i})) = {rlist(raw)} := by',
                      pre+f'  norm_num [List.finRange, List.ofFn_succ, {", ".join(syms)}]' if syms else pre+'  norm_num [List.finRange, List.ofFn_succ]',
                      pre+f'rw [he{i}] at hp{i}',
                      pre+f'have hperm{i} := hp{i}.trans ({old.permutation_term(raw,es)})',
                      pre+f'have hrow{i} : M.rowxs {i} = {rlist(es)} := hperm{i}.eq_of_pairwise\' (M.row_sorted {i}) hsort{i}',
                      pre+f'have hraw{i} := SmallScoreGapBounds.model_all_bounds M {i} {c} hdef{i}',
                      pre+f'simp only [SmallScoreGapBounds.modelGaps, hrow{i}, StrongGapBudget.linearGaps] at hraw{i}',
                      pre+f'norm_num only [Nat.cast_ofNat] at hraw{i}']
            for k,v in enumerate(values):
                lines += [pre+f'have hmax{i}{k} : {v} < {6-c} := by',
                          pre+f'  have h := hraw{i}.1 {v} (by simp)',pre+'  norm_num at h',pre+'  exact h']
            if c==3:lines += [pre+f'have hcount{i} : SmallScoreGapBounds.countAtLeast 2 [{", ".join(values)}] ≤ 1 := by',pre+f'  have h := hraw{i}.2.1',pre+'  omega']
            lines += [pre+f'have hbudget{i} := StrongGapBudget.defect_{"two" if c==2 else "three"}_budget M {i} hdef{i}'+(' (by decide)' if c==3 else ''),
                      pre+f'simp only [hrow{i}, StrongGapBudget.linearGaps] at hbudget{i}',
                      pre+f'norm_num only [Nat.cast_ofNat] at hbudget{i}',
                      pre+f'have hchoice{i} := N4StrongGapChoices.choices_{"two" if c==2 else "three"} '+ ' '.join(values)+f' hbudget{i}']
        return lines
    def render(node,indent=2,mask=None):
        pre=' '*indent
        if 'core' in node:return [pre+'linarith only ['+', '.join(node['core'])+']']
        if 'profile' in node:
            mask=node['profile'];return setup_profile(mask,indent)+render(node['child'],indent,mask)
        info=node['info'];lines=[]
        if node['kind']=='tri':
            i,j,k=info['ijk'];pat='⟨'+', '.join(info['names'])+'⟩'
            lines=[pre+f'rcases M.triangle {i} {j} {k} (by decide) (by decide) with {pat} | {pat}']
        else:
            i,c=info['i'],info['c'];gs=gap_strings(i,profiles[mask][i]);pairs=list(itertools.combinations(range(5),2))
            pats=[f'hb{i}0']*(5 if c==3 else 5)+(['⟨hb'+str(i)+'0, hb'+str(i)+'1⟩']*10 if c==2 else [])
            lines=[pre+f'rcases hchoice{i} with '+' | '.join(pats)]
        for arm,child in enumerate(node['children']):
            lines.append(pre+'·')
            if node['kind']=='row' and c==3:
                gs=gap_strings(i,profiles[mask][i]);other=[j for j in range(5) if j!=arm]
                for number,j in enumerate(other,1):
                    lo,hi=sorted((arm,j));term=sublist_term(gs,{lo,hi})
                    lines += [pre+f'  have hb{i}{number} : {gs[j]} < 2 := by',pre+'    by_contra hh',
                              pre+f'    have hother : 2 ≤ {gs[j]} := by linarith',
                              pre+'    have h := N4StrongGapChoices.two_large_of_sublist '+f'[{", ".join(gs)}] {gs[lo]} {gs[hi]} {term} '+('hb'+str(i)+'0 hother' if lo==arm else 'hother hb'+str(i)+'0'),
                              pre+'    omega']
            lines += render(child,indent+2,mask)
        return lines
    header='''import Jsp000404.N4StrongGapChoices

/-! Ordinary kernel certificate for the actual n=4 shared-chord model.
The diagnostic only selects finite splits and linarith premise subsets. -/
namespace Jsp404.N4StrongFourRowTerminal

set_option maxHeartbeats 48000000 in
theorem four_rows_impossible (M : SixModelCompression.ModelSix 4)
    (hhigh : (1/2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2) : False := by
  have hdelta0 := hhigh
  have hdelta1 := M.hdelta.2
'''
    setup=[]
    for i in range(5):
        setup.append(f'  obtain ⟨ht{i}a, ht{i}b⟩ := M.theta_bounds {i}')
        if i<4:setup.append(f'  have ht{i}{i+1} := M.htheta (show ({i} : Fin 5) < {i+1} from by decide)')
    for i,j in EDGES:
        setup.append(f'  obtain ⟨hc{i}{j}a, hc{i}{j}b⟩ := M.corridor {i} {j} (by decide)')
        setup.append(f'  norm_num at hc{i}{j}b')
    return header+'\n'.join(setup+render(tree))+'\n\n#print axioms four_rows_impossible\nend Jsp404.N4StrongFourRowTerminal\n'


if __name__=='__main__':main()
