#!/usr/bin/env python3
"""Prototype exact positive-score integer branch certificates, without MIP trust.

The diagnostic uses real score variables only to select zero/positive splits
and integer cuts.  Actual Lean variables are natural gap scores.  No Cartesian
product of row score compositions is expanded.  This first prototype is one
fixed strip/orientation; a future public wrapper must split all triangle arms.
"""
from fractions import Fraction
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import pickle
import re
import subprocess
import time

import z3

ROOT=Path(__file__).resolve().parents[1]
TRIPLES=list(itertools.combinations(range(5),3))
EDGES=list(itertools.combinations(range(5),2))


def row_orders(mask):
    closure={e:set() for e in EDGES}
    for bit,(i,j,k) in enumerate(TRIPLES):
        x,y,z=(i,j),(i,k),(j,k);lo,mid,hi=(z,y,x) if mask>>bit&1 else(x,y,z)
        closure[lo].add(mid);closure[mid].add(hi)
    for _ in range(10):closure={a:set(bs).union(*(closure[b] for b in bs)) for a,bs in closure.items()}
    if any(e in closure[e] for e in EDGES):return None
    rows={}
    for i in range(5):
        es=[tuple(sorted((i,j))) for j in range(5) if i!=j];old=tuple(es)
        es.sort(key=lambda e:sum(e in closure[f] for f in old));rows[i]=es
    return rows


class Exporter:
    def __init__(self,n,mask,profile,wall,nodes):
        self.n,self.mask,self.profile=n,mask,profile
        self.defects={0:2,1:3,3:3,4:2} if profile=='between' else {0:2,1:2,2:3,3:3,4:3}
        self.wall,self.limit,self.started=wall,nodes,time.monotonic()
        self.stats={'nodes':0,'linear_leaves':0,'zero_positive_splits':0,'integer_splits':0,'max_depth':0}
        self.de=z3.Real('delta');self.t=[z3.Real(f't{i}') for i in range(5)]
        self.d={e:z3.Real(f'd{e[0]}{e[1]}') for e in EDGES}
        self.s={i:[z3.Real(f's{i}{k}') for k in range(5)] for i in self.defects}
        self.rows=row_orders(mask);assert self.rows is not None
        self.gaps={i:self.gap_expr(i) for i in self.defects}
        self.base=self.geometry();self.pending={}
        for i,c in self.defects.items():
            self.base[f'hsum{i}']=z3.Sum(self.s[i])==n-c
            for k,(s,g) in enumerate(zip(self.s[i],self.gaps[i])):
                self.base[f'hnonneg{i}{k}']=g>=0
                self.base[f'hscore{i}{k}a']=s>=0
                self.base[f'hscore{i}{k}b']=s<=n-c
                self.pending[f'gap{i}{k}']={'i':i,'k':k,'arms':[[s==0,g<2],[s>=1,s+1<=g,g<s+2]]}

    def fingerprint_payload(self):
        """All mathematical premises that give a cached tree its meaning."""
        return {'schema':'positive-gap-score-tree-v1','n':self.n,
                'profile':self.profile,'mask':self.mask,
                'defects':self.defects,'sorted_rows':self.rows,
                'triangle_order':TRIPLES,
                'base':[(key,value.sexpr()) for key,value in self.base.items()],
                'pending':[(key,[[x.sexpr() for x in arm] for arm in value['arms']])
                           for key,value in self.pending.items()]}

    def fingerprint(self):
        payload=json.dumps(self.fingerprint_payload(),sort_keys=True,separators=(',',':'))
        return hashlib.sha256(payload.encode()).hexdigest()

    def cache_path(self):
        return Path('/tmp')/f'jsp404_six_exact_score_{self.n}_{self.profile}_{self.mask}_{self.fingerprint()}.pkl'

    def audit_tree(self,tree):
        """Reconstruct branch premises; this is provenance, not a proof checker."""
        leaves=[];cuts=[]
        def walk(node,base,pending,path):
            if 'core' in node:
                assert set(node['core']).issubset(base),('unknown leaf premise',path)
                constraints=[(name,expr.sexpr()) for name,expr in sorted(base.items())]
                payload=json.dumps(constraints,separators=(',',':')).encode()
                leaves.append({'path':path,'core':node['core'],
                               'all_constraints_sha256':hashlib.sha256(payload).hexdigest()})
                return
            assert len(node['children'])==2,('branch coverage missing',path)
            i,k=node['i'],node['k']
            if node['kind']=='zero_positive':
                name=f'gap{i}{k}';info=pending[name]
                remaining={key:value for key,value in pending.items() if key!=name}
                for arm,values in enumerate(info['arms']):
                    names=[f'hgap{i}{k}{s}' for s in ('ab' if arm==0 else 'abc')]
                    walk(node['children'][arm],{**base,**dict(zip(names,values))},remaining,path+str(arm))
            else:
                assert node['kind']=='integer'
                cut=node['cut'];assert isinstance(cut,int)
                name=f'hcut{i}{k}_{cut}';s=self.s[i][k]
                values=[s<=cut,s>=cut+1]
                cuts.append({'path':path,'score':f's{i}{k}','cut':cut,
                             'arms':[value.sexpr() for value in values]})
                for arm,value in enumerate(values):
                    walk(node['children'][arm],{**base,name:value},pending,path+str(arm))
        walk(tree,self.base,self.pending,'')
        payload={'root_fingerprint_sha256':self.fingerprint(),'leaves':leaves,'integer_cuts':cuts}
        encoded=json.dumps(payload,sort_keys=True,separators=(',',':')).encode()
        return {**payload,'all_leaf_constraints_sha256':hashlib.sha256(encoded).hexdigest()}

    def gap_expr(self,i):
        xs=[self.d[e] for e in self.rows[i]]
        return [xs[0]-self.t[i]]+[xs[k+1]-xs[k] for k in range(3)]+[self.t[i]+self.n+self.de-xs[3]]

    def geometry(self):
        a={'hdelta0':self.de>=z3.RealVal('1/2'),'hdelta1':self.de<1}
        for i in range(5):
            a[f'ht{i}a'],a[f'ht{i}b']=self.t[i]>=0,self.t[i]<=self.de
            if i<4:a[f'ht{i}{i+1}']=self.t[i]<self.t[i+1]
        for (i,j),d in self.d.items():a[f'hc{i}{j}a'],a[f'hc{i}{j}b']=self.t[i]+1<=d,d<=self.n+self.de-1+self.t[j]
        for bit,(i,j,k) in enumerate(TRIPLES):
            x,y,z=self.d[i,j],self.d[i,k],self.d[j,k];lo,hi=(z,x) if self.mask>>bit&1 else(x,z)
            a[f'htr{i}{j}{k}a'],a[f'htr{i}{j}{k}b'],a[f'htr{i}{j}{k}c']=lo+1<=hi,lo<y,y<hi
        return a

    def solve(self,base,pending):
        solver=z3.SolverFor('QF_LRA');solver.set(timeout=1500,random_seed=0)
        for name,x in base.items():solver.assert_and_track(x,z3.Bool(name))
        for name,info in pending.items():solver.assert_and_track(z3.Or(*[z3.And(*a) for a in info['arms']]),z3.Bool(name))
        status=solver.check()
        if status==z3.unknown:raise RuntimeError(solver.reason_unknown())
        return status,([str(x) for x in solver.unsat_core()] if status==z3.unsat else solver.model())

    def tree(self,base,pending,depth=0):
        if self.stats['nodes']>=self.limit or time.monotonic()-self.started>self.wall:raise TimeoutError('generation budget exhausted')
        self.stats['nodes']+=1;self.stats['max_depth']=max(depth,self.stats['max_depth'])
        status,core=self.solve(base,{})
        if status==z3.unsat:
            self.stats['linear_leaves']+=1;return {'core':core}
        if pending:
            status,core=self.solve(base,pending)
            candidates=[name for name in core if name in pending] if status==z3.unsat else list(pending)
            if candidates:
                chosen=min(candidates);info=pending[chosen];i,k=info['i'],info['k']
                remaining={name:val for name,val in pending.items() if name!=chosen}
                self.stats['zero_positive_splits']+=1;children=[]
                for arm,values in enumerate(info['arms']):
                    names=[f'hgap{i}{k}{s}' for s in ('ab' if arm==0 else 'abc')]
                    children.append(self.tree({**base,**dict(zip(names,values))},remaining,depth+1))
                return {'kind':'zero_positive','i':i,'k':k,'children':children}
        status,model=self.solve(base,{})
        fractional=[]
        for i,ss in self.s.items():
            for k,s in enumerate(ss):
                value=model.eval(s,model_completion=True);q=Fraction(value.numerator_as_long(),value.denominator_as_long())
                if q.denominator!=1:fractional.append((i,k,q))
        if not fractional:raise RuntimeError('exact integer-score SAT branch reached; not a point claim')
        i,k,q=min(fractional,key=lambda e:(e[2].denominator,e[0],e[1]));cut=q.numerator//q.denominator
        self.stats['integer_splits']+=1
        s=self.s[i][k];name=f'hcut{i}{k}_{cut}'
        children=[self.tree({**base,name:s<=cut},pending,depth+1),self.tree({**base,name:s>=cut+1},pending,depth+1)]
        return {'kind':'integer','i':i,'k':k,'cut':cut,'children':children}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',type=int,default=5);parser.add_argument('--mask',type=int,default=0)
    parser.add_argument('--profile',choices=['between','front'],default='between')
    parser.add_argument('--wall-seconds',type=float,default=28);parser.add_argument('--max-nodes',type=int,default=4000)
    parser.add_argument('--emit-cached',action='store_true')
    parser.add_argument('--estimate-all',action='store_true',help='Estimate all 62 acyclic orientations without emitting Lean')
    parser.add_argument('--batch-wall-seconds',type=float,default=55)
    parser.add_argument('--emit-all-cached',action='store_true')
    parser.add_argument('--strict-all',action='store_true')
    parser.add_argument('--normal-all',action='store_true')
    parser.add_argument('--max-leaves-per-module',type=int,default=300)
    args=parser.parse_args()
    if args.estimate_all:
        estimate_all(args);return
    if args.emit_all_cached:
        emit_all_cached(args);return
    if args.strict_all or args.normal_all:
        check_all(args,'strict' if args.strict_all else 'normal');return
    e=Exporter(args.n,args.mask,args.profile,args.wall_seconds,args.max_nodes)
    if args.emit_cached:
        with e.cache_path().open('rb') as source:cached=pickle.load(source)
        assert cached['fingerprint']==e.fingerprint()
        assert cached['fingerprint_payload']==e.fingerprint_payload()
        assert cached['audit']==e.audit_tree(cached['tree'])
        text=emit_probe(e,cached['tree']);path=ROOT/'Jsp000404/SixExactFloorKernelProbe.lean';path.write_text(text)
        report={**cached['report'],'source':str(path),'source_lines':len(text.splitlines()),'source_bytes':len(text.encode()),'kernel':'NOT_RUN'}
        (ROOT/'research/JSP404_SIX_SCORE_KERNEL_PROBE_20261005.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report));return
    try:tree=e.tree(e.base,e.pending);status='COMPLETE_TREE'
    except (TimeoutError,RuntimeError) as exc:tree=None;status=str(exc)
    report={'n':args.n,'mask':args.mask,'profile':args.profile,**e.stats,'status':status,
            'seconds':time.monotonic()-e.started,'kernel':'NOT_RUN','no_integer_solver_trusted':True,
            'constraint_fingerprint_sha256':e.fingerprint(),
            'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    path=ROOT/f'research/JSP404_SIX_SCORE_EXPORT_PROBE_N{args.n}_M{args.mask}_20261005.json';path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)
    if tree is not None:
        audit=e.audit_tree(tree)
        with e.cache_path().open('wb') as output:
            pickle.dump({'tree':tree,'rows':e.rows,'report':report,
                         'fingerprint':e.fingerprint(),
                         'fingerprint_payload':e.fingerprint_payload(),'audit':audit},output)
        audit_path=ROOT/f'research/JSP404_SIX_SCORE_TREE_N{args.n}_{args.profile}_M{args.mask}_20261005.json'
        audit_path.write_text(json.dumps({'report':report,'root_constraints':e.fingerprint_payload(),
                                         'tree':tree,'audit':audit,'solver_seed':0},indent=2)+'\n')


def estimate_all(args):
    """Size-only bounded run: no Lean generation and no proof claim."""
    started=time.monotonic();results=[]
    masks=[mask for mask in range(1024) if row_orders(mask) is not None]
    assert len(masks)==62
    for mask in masks:
        remaining=args.batch_wall_seconds-(time.monotonic()-started)
        if remaining<=0:break
        e=Exporter(args.n,mask,args.profile,min(args.wall_seconds,remaining),args.max_nodes)
        tree=None;cached=False
        if e.cache_path().exists():
            with e.cache_path().open('rb') as source:data=pickle.load(source)
            assert data['fingerprint']==e.fingerprint()
            assert data['fingerprint_payload']==e.fingerprint_payload()
            assert data['audit']==e.audit_tree(data['tree'])
            tree=data['tree'];stats={key:data['report'][key] for key in e.stats};status='COMPLETE_TREE';cached=True
        else:
            try:tree=e.tree(e.base,e.pending);status='COMPLETE_TREE'
            except (TimeoutError,RuntimeError) as exc:status=str(exc)
            stats=e.stats
        report={'n':args.n,'profile':args.profile,'mask':mask,**stats,'status':status,
                'seconds':time.monotonic()-e.started,'cached':cached,'kernel':'NOT_RUN',
                'constraint_fingerprint_sha256':e.fingerprint(),
                'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
        results.append(report)
        if tree is not None and not cached:
            audit=e.audit_tree(tree)
            with e.cache_path().open('wb') as output:
                pickle.dump({'tree':tree,'rows':e.rows,'report':report,
                             'fingerprint':e.fingerprint(),
                             'fingerprint_payload':e.fingerprint_payload(),'audit':audit},output)
        completed=[case for case in results if case['status']=='COMPLETE_TREE']
        summary={'n':args.n,'profile':args.profile,'status':'COMPLETE_SIZE_COVERAGE' if len(completed)==62 else 'PARTIAL_SIZE_COVERAGE',
                 'orientation_masks':masks,'completed_masks':[case['mask'] for case in completed],
                 'unvisited_masks':masks[len(results):],
                 'total_nodes':sum(case['nodes'] for case in completed),
                 'total_leaves':sum(case['linear_leaves'] for case in completed),
                 'total_integer_cuts':sum(case['integer_splits'] for case in completed),
                 'seconds':time.monotonic()-started,'results':results,
                 'kernel':'NOT_RUN','source_generation':'NOT_RUN',
                 'public_coverage':'Not generated. A public theorem must additionally close all cyclic triangle arms by ordinary Lean arithmetic.'}
        target=ROOT/f'research/JSP404_SIX_SCORE_SIZE_N{args.n}_{args.profile}_20261005.json'
        target.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({key:value for key,value in summary.items() if key!='results'}),flush=True)


def emit_probe(e,tree,theorem_name='representative_probe'):
    import export_four_row_certificate_20261004 as old
    def ch(edge):return f'M.d {edge[0]} {edge[1]}'
    def li(edges):return '['+', '.join(ch(edge) for edge in edges)+']'
    def gaps(i):
        xs=[ch(edge) for edge in e.rows[i]]
        return [f'({xs[0]} - M.theta {i})']+[f'({xs[k+1]} - {xs[k]})' for k in range(3)]+[f'(M.theta {i} + ({e.n} + M.delta) - {xs[3]})']
    header=['import Jsp000404.SixExactFloorKernelPrimitives','',
            '/-! Representative exact-score certificate. A fixed orientation is an explicit',
            'hypothesis only for this probe; public wrappers must split every triangle arm. -/',
            'namespace Jsp404.SixExactFloorKernel','',
            'set_option maxHeartbeats 16000000 in',
            f'theorem {theorem_name} (M : SixModelCompression.ModelSix {e.n})',
            '    (hhigh : (1/2 : ℝ) ≤ M.delta)']
    header += [f'    (hdef{i} : SixModelCompression.rowDefect M {i} = {c})' for i,c in e.defects.items()]
    for bit,(i,j,k) in enumerate(TRIPLES):
        x,y,z=ch((i,j)),ch((i,k)),ch((j,k));lo,hi=(z,x) if e.mask>>bit&1 else(x,z)
        header += [f'    (htri{i}{j}{k} : {lo}+1 ≤ {hi} ∧ {lo} < {y} ∧ {y} < {hi})']
    header += ['    : False := by','  have hdelta0 := hhigh','  have hdelta1 := M.hdelta.2']
    for i in range(5):
        header += [f'  obtain ⟨ht{i}a, ht{i}b⟩ := M.theta_bounds {i}']
        if i<4:header += [f'  have ht{i}{i+1} := M.htheta (show ({i} : Fin 5) < {i+1} from by decide)']
    for i,j in EDGES:header += [f'  obtain ⟨hc{i}{j}a, hc{i}{j}b⟩ := M.corridor {i} {j} (by decide)',f'  norm_num at hc{i}{j}b']
    for i,j,k in TRIPLES:header += [f'  obtain ⟨htr{i}{j}{k}a, htr{i}{j}{k}b, htr{i}{j}{k}c⟩ := htri{i}{j}{k}']
    for i,c in e.defects.items():
        es=e.rows[i];raw=[tuple(sorted((i,j))) for j in range(5) if i!=j];gs=gaps(i);ss=[f's{i}{k}' for k in range(5)]
        header += [f'  have hsort{i} : ({li(es)} : List ℝ).Pairwise (· ≤ ·) := by',
                   '    simp [List.pairwise_cons]','    repeat\' apply And.intro','    all_goals linarith']
        header += [f'  have hp{i} := M.row_perm {i}'];syms=[]
        for j in range(i):
            syms += [f'hcanon{i}{j}'];header += [f'  have hcanon{i}{j} : M.d {i} {j} = M.d {j} {i} := M.symm {i} {j} (by decide)']
        header += [f'  have he{i} : (((List.finRange 5).erase ({i} : Fin 5)).map (M.d {i})) = {li(raw)} := by',
                   '    norm_num [List.finRange, List.ofFn_succ'+(', '+', '.join(syms) if syms else '')+']',
                   f'  rw [he{i}] at hp{i}',f'  have hperm{i} := hp{i}.trans ({old.permutation_term(raw,es)})',
                   f'  have hrow{i} : M.rowxs {i} = {li(es)} := hperm{i}.eq_of_pairwise\' (M.row_sorted {i}) hsort{i}',
                   f'  have hrow_nonneg{i} := SmallScoreGapBounds.model_gaps_nonneg M {i}',
                   f'  simp only [SmallScoreGapBounds.modelGaps, hrow{i}, StrongGapBudget.linearGaps] at hrow_nonneg{i}',
                   f'  norm_num only [Nat.cast_ofNat] at hrow_nonneg{i}']
        for k,(g,s) in enumerate(zip(gs,ss)):
            header += [f'  let {s} : ℕ := ⌊{g}⌋₊ - 1',
                       f'  have hnonneg{i}{k} : 0 ≤ {g} := hrow_nonneg{i} {g} (by simp)',
                       f'  have hscore{i}{k}a : (0 : ℝ) ≤ {s} := Nat.cast_nonneg {s}',
                       f'  have hbridge{i}{k} := score_gap_dichotomy {g} hnonneg{i}{k}',
                       f'  change ({s} = 0 ∧ {g} < 2) ∨ (1 ≤ {s} ∧ ({s} : ℝ)+1 ≤ {g} ∧ {g} < ({s} : ℝ)+2) at hbridge{i}{k}']
        nat_sum=ss[-1]
        for s in reversed(ss[:-1]):nat_sum=f'{s} + ({nat_sum})'
        real_sum=f'({ss[-1]} : ℝ)'
        for s in reversed(ss[:-1]):real_sum=f'({s} : ℝ) + ({real_sum})'
        nat_sum_zero=f'{ss[0]} + ({ss[1]} + ({ss[2]} + ({ss[3]} + ({ss[4]} + 0))))'
        header += [f'  have hsum_nat{i} : {nat_sum} = {e.n-c} := by',
                   f'    have h := SmallScoreGapBounds.model_score M {i} {c} hdef{i}',
                   f'    simp only [SmallScoreGapBounds.modelGaps, hrow{i}, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h',
                   f'    change ({nat_sum_zero}) + {c} = {e.n} at h','    omega',
                   f'  have hsum{i} : {real_sum} = {e.n-c} := by',
                   f'    have h : '+nat_sum.replace('s','s')+f' = {e.n-c} := hsum_nat{i}',
                   '    exact_mod_cast h']
        for k,s in enumerate(ss):
            header += [f'  have hscore{i}{k}b : ({s} : ℝ) ≤ {e.n-c} := by',
                       f'    have h : {s} ≤ {e.n-c} := by omega','    exact_mod_cast h']
    def render(node,indent=2):
        pre=' '*indent
        if 'core' in node:return [pre+'linarith only ['+', '.join(node['core'])+']']
        i,k=node['i'],node['k'];s=f's{i}{k}';gs=gaps(i);g=gs[k]
        if node['kind']=='zero_positive':
            lines=[pre+f'rcases hbridge{i}{k} with ⟨hzero{i}{k}, hgap{i}{k}b⟩ | ⟨hpositive{i}{k}, hgap{i}{k}b, hgap{i}{k}c⟩']
            lines += [pre+'·',pre+f'  have hgap{i}{k}a : ({s} : ℝ) = 0 := by exact_mod_cast hzero{i}{k}']
            lines += render(node['children'][0],indent+2)
            lines += [pre+'·',pre+f'  have hgap{i}{k}a : (1 : ℝ) ≤ {s} := by exact_mod_cast hpositive{i}{k}']
            lines += render(node['children'][1],indent+2)
            return lines
        cut=node['cut'];name=f'hcut{i}{k}_{cut}'
        lines=[pre+f'by_cases {name}nat : {s} ≤ {cut}',pre+'·',pre+f'  have {name} : ({s} : ℝ) ≤ {cut} := by exact_mod_cast {name}nat']
        lines += render(node['children'][0],indent+2)
        lines += [pre+'·',pre+f'  have {name}natpos : {cut+1} ≤ {s} := by omega',pre+f'  have {name} : ({cut+1} : ℝ) ≤ {s} := by exact_mod_cast {name}natpos']
        lines += render(node['children'][1],indent+2)
        return lines
    return '\n'.join(header+render(tree))+f'\n\n#print axioms {theorem_name}\nend Jsp404.SixExactFloorKernel\n'


def orientation_theorem(n,profile,mask):
    return f'n{n}_{profile}_mask{mask:03d}'


def orientation_module(n,profile,mask):
    return f'SixExactFloorKernelN{n}{profile.title()}M{mask:03d}'


def coverage_tree():
    """All ten original Or hypotheses, including ordinary arithmetic cycle leaves."""
    d={edge:z3.Real(f'd{edge[0]}{edge[1]}') for edge in EDGES}
    stats={'splits':0,'cycle_leaves':0,'orientation_leaves':0,'full_arms_covered':0}
    def tree(base,bit,mask):
        solver=z3.SolverFor('QF_LRA');solver.set(timeout=1500,random_seed=0)
        for name,expr in base.items():solver.assert_and_track(expr,z3.Bool(name))
        status=solver.check()
        if status==z3.unknown:raise RuntimeError(solver.reason_unknown())
        if status==z3.unsat:
            core=[str(x) for x in solver.unsat_core()]
            assert set(core).issubset(base)
            stats['cycle_leaves']+=1;stats['full_arms_covered']+=2**(10-bit)
            return {'core':core,'covered_full_arms':2**(10-bit)}
        if bit==10:
            assert row_orders(mask) is not None
            stats['orientation_leaves']+=1;stats['full_arms_covered']+=1
            return {'mask':mask,'covered_full_arms':1}
        i,j,k=TRIPLES[bit];x,y,z=d[i,j],d[i,k],d[j,k]
        names=[f'htr{i}{j}{k}{suffix}' for suffix in 'abc']
        arms=[[x+1<=z,x<y,y<z],[z+1<=x,z<y,y<x]]
        stats['splits']+=1
        children=[tree({**base,**dict(zip(names,arm))},bit+1,mask|(arm_index<<bit)) for arm_index,arm in enumerate(arms)]
        return {'triple':[i,j,k],'children':children}
    result=tree({},0,0)
    assert stats['orientation_leaves']==62 and stats['full_arms_covered']==1024
    return result,stats


def emit_terminal(n,profile,tree):
    masks=[mask for mask in range(1024) if row_orders(mask) is not None]
    defects={0:2,1:3,3:3,4:2} if profile=='between' else {0:2,1:2,2:3,3:3,4:3}
    header=[f'import Jsp000404.{orientation_module(n,profile,mask)}' for mask in masks]
    header+=['','/-! Complete ten-triangle disjunction coverage. No acyclic-orientation hypothesis. -/',
             'namespace Jsp404.SixExactFloorKernel','',
             'set_option maxHeartbeats 16000000 in',
             f'theorem n{n}_{profile}_impossible (M : SixModelCompression.ModelSix {n})',
             '    (hhigh : (1/2 : ℝ) ≤ M.delta)']
    header += [f'    (hdef{i} : SixModelCompression.rowDefect M {i} = {c})' for i,c in defects.items()]
    header += ['    : False := by']
    def render(node,indent=2):
        pre=' '*indent
        if 'core' in node:return [pre+'linarith only ['+', '.join(node['core'])+']']
        if 'mask' in node:
            args=['M','hhigh']+[f'hdef{i}' for i in defects]+[f'htri{i}{j}{k}' for i,j,k in TRIPLES]
            return [pre+f'exact {orientation_theorem(n,profile,node["mask"])} '+' '.join(args)]
        i,j,k=node['triple'];name=f'htri{i}{j}{k}'
        lines=[pre+f'rcases M.triangle {i} {j} {k} (by decide) (by decide) with {name} | {name}']
        for child in node['children']:
            lines += [pre+'·',pre+f'  have htr{i}{j}{k}a := {name}.1',
                      pre+f'  have htr{i}{j}{k}b := {name}.2.1',
                      pre+f'  have htr{i}{j}{k}c := {name}.2.2']
            lines += render(child,indent+2)
        return lines
    return '\n'.join(header+render(tree))+f'\n\n#print axioms n{n}_{profile}_impossible\nend Jsp404.SixExactFloorKernel\n'


def manifest_path(n,profile):
    return ROOT/f'research/JSP404_SIX_SCORE_N{n}_{profile.upper()}_MANIFEST_20261005.json'


def emit_all_cached(args):
    masks=[mask for mask in range(1024) if row_orders(mask) is not None]
    prepared=[]
    for mask in masks:
        e=Exporter(args.n,mask,args.profile,1,1)
        with e.cache_path().open('rb') as source:data=pickle.load(source)
        assert data['fingerprint']==e.fingerprint()
        assert data['fingerprint_payload']==e.fingerprint_payload()
        audit=e.audit_tree(data['tree']);assert data['audit']==audit
        assert len(audit['leaves'])<=args.max_leaves_per_module
        theorem=orientation_theorem(args.n,args.profile,mask)
        module=orientation_module(args.n,args.profile,mask)
        source=emit_probe(e,data['tree'],theorem)
        prepared.append((module,theorem,source,{'mask':mask,'root_constraints':e.fingerprint_payload(),
                                               'tree':data['tree'],'audit':audit,'solver_seed':0}))
    tree,coverage=coverage_tree()
    module=f'SixExactFloorKernelN{args.n}{args.profile.title()}Terminal'
    prepared.append((module,f'n{args.n}_{args.profile}_impossible',emit_terminal(args.n,args.profile,tree),
                     {'tree':tree,'coverage':coverage,'solver_seed':0}))
    audit_dir=ROOT/f'research/six-score-n{args.n}-{args.profile}-20261005'
    audit_dir.mkdir(exist_ok=True)
    modules=[]
    for module,theorem,source,audit in prepared:
        relative=f'Jsp000404/{module}.lean';path=ROOT/relative
        path.write_text(source)
        audit_path=audit_dir/f'{module}.json';audit_path.write_text(json.dumps(audit,indent=2)+'\n')
        modules.append({'module':f'Jsp000404.{module}','theorem':f'Jsp404.SixExactFloorKernel.{theorem}',
                        'source':relative,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                        'source_lines':len(source.splitlines()),'source_bytes':len(source.encode()),
                        'provenance':str(audit_path.relative_to(ROOT)),
                        'provenance_sha256':hashlib.sha256(audit_path.read_bytes()).hexdigest(),
                        'kernel':'NOT_RUN','normal_lake':'NOT_RUN'})
    dependencies=['Jsp000404/SixModelCompression.lean','Jsp000404/SixExactFloorKernelPrimitives.lean']
    manifest={'schema':'exact-score-bounded-kernel-v1','n':args.n,'profile':args.profile,
              'scope':'HIGH necessary ModelSix four-row critical domain only; no full strip capacity or all-N theorem.',
              'sources_frozen':True,'modules':modules,'coverage':coverage,
              'dependency_sources':{path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in dependencies},
              'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'all_kernels':'NOT_RUN','all_normal_lake':'NOT_RUN'}
    manifest_path(args.n,args.profile).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'modules':len(modules),'source_lines':sum(m['source_lines'] for m in modules),
                      'source_bytes':sum(m['source_bytes'] for m in modules),'coverage':coverage}),flush=True)


def process_rss_kib(pid):
    output=subprocess.run(['ps','-A','-o','pid=,ppid=,rss='],capture_output=True,text=True,check=True).stdout
    processes=[tuple(map(int,line.split())) for line in output.splitlines() if line.strip()]
    own={pid}
    for _ in range(len(processes)):
        updated=own|{child for child,parent,_ in processes if parent in own}
        if updated==own:break
        own=updated
    return sum(rss for child,_,rss in processes if child in own)


def check_all(args,mode):
    """Sequential real compiler/Lake calls; never writes Lake metadata itself."""
    path=manifest_path(args.n,args.profile);manifest=json.loads(path.read_text())
    for relative,expected in manifest['dependency_sources'].items():
        assert hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()==expected
    for module in manifest['modules']:
        assert hashlib.sha256((ROOT/module['source']).read_bytes()).hexdigest()==module['source_sha256']
    log_dir=ROOT/f'verification/six-score-n{args.n}-{args.profile}-{mode}-20261005'
    log_dir.mkdir(exist_ok=True)
    receipt_path=ROOT/f'research/JSP404_SIX_SCORE_N{args.n}_{args.profile.upper()}_{mode.upper()}_RECEIPT_20261005.json'
    if receipt_path.exists():receipt=json.loads(receipt_path.read_text())
    else:receipt={'mode':mode,'status':'RUNNING','concurrency':1,'rss_admission_limit_kib':6*1024*1024,'results':[]}
    recorded={result['module']:result for result in receipt['results']}
    targets=[{'module':relative[:-5].replace('/','.'),'source':relative,'source_sha256':sha}
             for relative,sha in manifest['dependency_sources'].items()]+manifest['modules']
    for target in targets:
        old=recorded.get(target['module'])
        artifact=ROOT/'.lake/build/lib/lean'/Path(target['source']).with_suffix('.olean')
        if (old and old['status']=='PASS' and old['source_sha256']==target['source_sha256']
                and artifact.exists() and hashlib.sha256(artifact.read_bytes()).hexdigest()==old.get('artifact_sha256')):continue
        module=target['module'];log_path=log_dir/f'{module.rsplit(".",1)[1]}.txt'
        command=(['lake','env','lean','--trust=0','-DautoImplicit=false','-o',str(artifact),target['source']]
                 if mode=='strict' else ['lake','build',module])
        started=time.monotonic();peak=0
        with log_path.open('w') as log:
            proc=subprocess.Popen(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
            while proc.poll() is None:
                peak=max(peak,process_rss_kib(proc.pid));time.sleep(.25)
            code=proc.returncode
        output=log_path.read_text();axioms=re.findall(r"depends on axioms: \[([^\]]*)\]",output)
        standard={'propext','Classical.choice','Quot.sound'}
        bad_axioms=[value for value in axioms if not set(value.replace(',',' ').split()).issubset(standard)]
        ok=code==0 and 'error:' not in output and not bad_axioms and artifact.exists()
        if mode=='strict':ok=ok and bool(axioms)
        result={'module':module,'source_sha256':target['source_sha256'],'status':'PASS' if ok else 'FAIL',
                'exit_code':code,'seconds':time.monotonic()-started,'peak_process_tree_rss_kib':peak,
                'command':command,'axioms':axioms,'log':str(log_path.relative_to(ROOT)),
                'log_sha256':hashlib.sha256(log_path.read_bytes()).hexdigest(),
                'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest() if artifact.exists() else None}
        receipt['results']=[item for item in receipt['results'] if item['module']!=module]+[result]
        receipt['completed']=sum(item['status']=='PASS' for item in receipt['results'])
        receipt['status']='RUNNING' if ok else 'FAIL'
        receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps({key:result[key] for key in ('module','status','seconds','peak_process_tree_rss_kib')}),flush=True)
        if not ok:raise RuntimeError(f'{mode} failed for {module}; dispatch stopped')
    receipt['status']='PASS';receipt['expected_targets']=len(targets)
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
    manifest['all_kernels' if mode=='strict' else 'all_normal_lake']='PASS'
    for module in manifest['modules']:module['kernel' if mode=='strict' else 'normal_lake']='PASS'
    path.write_text(json.dumps(manifest,indent=2)+'\n')


if __name__=='__main__':main()
