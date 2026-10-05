#!/usr/bin/env python3
"""Exact symbolic-score cycle cuts, diagnostic until ordinary Lean checks them.

Only one fixed triangle orientation is handled by this prototype.  A score
candidate is chosen by integer arithmetic; exact strict DBM negative cycles
exclude it through symbolic cuts whose coefficients never use that candidate.
"""
from dataclasses import dataclass
from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path
import time

import z3
from export_six_exact_floor_kernel_20261005 import EDGES,TRIPLES,row_orders

ROOT=Path(__file__).resolve().parents[1]
DEFECTS={0:2,1:3,3:3,4:2}
NAMES=['n']+[f's{i}{k}' for i in DEFECTS for k in range(5)]
INDEX={name:index for index,name in enumerate(NAMES)}

@dataclass(frozen=True)
class Affine:
    coefficients:tuple
    constant:int=0
    def __add__(self,other):
        return Affine(tuple(a+b for a,b in zip(self.coefficients,other.coefficients)),self.constant+other.constant)
    def scale(self,k):return Affine(tuple(k*a for a in self.coefficients),k*self.constant)
    def evaluate(self,values):return self.constant+sum(c*values[n] for n,c in zip(NAMES,self.coefficients))
    def serial(self):return {'coefficients':dict((name,c) for name,c in zip(NAMES,self.coefficients) if c),'constant':self.constant}
    def z3(self,variables):return self.constant+z3.Sum([c*variables[name] for name,c in zip(NAMES,self.coefficients) if c])

def affine(name=None,c=0):
    coefficients=[0]*len(NAMES)
    if name is not None:coefficients[INDEX[name]]=1
    return Affine(tuple(coefficients),c)

@dataclass(frozen=True)
class Arc:
    source:int
    target:int
    a:Affine
    b:int
    strict:bool
    premise:str
    phase:tuple|None=None
    def serial(self):return {'source':self.source,'target':self.target,'A':self.a.serial(),'B':self.b,'strict':self.strict,'premise':self.premise,'phase':self.phase}

@dataclass(frozen=True)
class Cycle:
    a:Affine
    b:int
    strict:bool
    arc_ids:tuple
    range_premise:str|None=None
    def serial(self):return {'A':self.a.serial(),'B':self.b,'strict':self.strict,'arc_ids':self.arc_ids,'range_premise':self.range_premise}

class Probe:
    def __init__(self,mask=0,upper=None,preorders=False,min_domain=False):
        self.mask,self.upper,self.use_preorders,self.min_domain=mask,upper,preorders,min_domain
        self.rows=row_orders(mask);assert self.rows is not None
        self.vertices=['zero']+[f't{i}' for i in range(5)]+[f'd{i}{j}' for i,j in EDGES]
        self.vertex={name:index for index,name in enumerate(self.vertices)}
        self.variables={name:z3.Int(name) for name in NAMES}
        self.base={'hn4':self.variables['n']>=4}
        if upper is not None:self.base['hnupper']=self.variables['n']<=upper
        for i,c in DEFECTS.items():
            self.base[f'hsum_nat{i}']=z3.Sum([self.variables[f's{i}{k}'] for k in range(5)])+c==self.variables['n']
            for k in range(5):
                s=self.variables[f's{i}{k}'];self.base[f'hscore_nat{i}{k}']=s>=0
                if min_domain:self.base[f'hmin_nat{i}{k}']=self.variables[f'u{i}{k}']==z3.If(s>=1,1,0)
        self.master=z3.SolverFor('QF_LIA');self.master.set(timeout=4000,random_seed=0)
        for name,value in self.base.items():self.master.assert_and_track(value,z3.Bool(name))
        self.cuts=[];self.stats={'candidates':0,'cycles':0,'dbm_runs':0,'learned_cuts':0}
        self.orders=self.preorders() if preorders else []
        for order in self.orders:
            self.master.assert_and_track(self.variables[order['left']]<=self.variables[order['right']],z3.Bool(order['name']))

    def preorders(self):
        """True geometric gap orders give unconditional natural floor orders."""
        real={name:z3.Real(name) for name in self.vertices if name!='zero'}
        real['zero']=z3.RealVal(0);real['n']=z3.Real('n_real');real['delta']=z3.Real('delta')
        zero={name:0 for name in NAMES}
        arcs=[arc for arc in self.geometry(zero) if arc.phase is None and
              all(not c for name,c in zip(NAMES,arc.a.coefficients) if name!='n')]
        solver=z3.SolverFor('QF_LRA');solver.set(timeout=1500,random_seed=0)
        facts={'hn4real':real['n']>=4,'hdelta0':real['delta']>=z3.RealVal('1/2'),'hdelta1':real['delta']<1}
        for arc in arcs:
            a=arc.a.constant+z3.Sum([c*real[name] for name,c in zip(NAMES,arc.a.coefficients) if c])
            difference=real[self.vertices[arc.target]]-real[self.vertices[arc.source]]
            facts[arc.premise]=difference<a+arc.b*real['delta'] if arc.strict else difference<=a+arc.b*real['delta']
        for name,value in facts.items():solver.assert_and_track(value,z3.Bool(name))
        gaps={}
        for i in DEFECTS:
            ds=[real[f'd{a}{b}'] for a,b in self.rows[i]]
            for k in range(5):
                gaps[f's{i}{k}']=(ds[0]-real[f't{i}'] if k==0 else
                    real[f't{i}']+real['n']+real['delta']-ds[3] if k==4 else ds[k]-ds[k-1])
        orders=[]
        for left in gaps:
            for right in gaps:
                if left==right:continue
                solver.push();solver.assert_and_track(gaps[left]>gaps[right],z3.Bool('neg_gap_order'))
                status=solver.check()
                if status==z3.unknown:raise RuntimeError(solver.reason_unknown())
                if status==z3.unsat:
                    core=[str(x) for x in solver.unsat_core() if str(x)!='neg_gap_order']
                    orders.append({'name':f'horder{len(orders)}','left':left,'right':right,'core':core})
                solver.pop()
        return orders

    def geometry(self,values):
        arcs=[];v=self.vertex;n=affine('n')
        def edge(source,target,a,b,strict,premise,phase=None):arcs.append(Arc(v[source],v[target],a,b,strict,premise,phase))
        for i in range(5):
            edge(f't{i}','zero',affine(),0,False,f'ht{i}a')
            edge('zero',f't{i}',affine(),1,False,f'ht{i}b')
            if i<4:edge(f't{i+1}',f't{i}',affine(),0,True,f'ht{i}{i+1}')
        for i,j in EDGES:
            edge(f'd{i}{j}',f't{i}',affine(c=-1),0,False,f'hc{i}{j}a')
            edge(f't{j}',f'd{i}{j}',n+affine(c=-1),1,False,f'hc{i}{j}b')
        for bit,(i,j,k) in enumerate(TRIPLES):
            x,y,z=f'd{i}{j}',f'd{i}{k}',f'd{j}{k}';lo,hi=(z,x) if self.mask>>bit&1 else(x,z)
            edge(hi,lo,affine(c=-1),0,False,f'htr{i}{j}{k}a')
            edge(y,lo,affine(),0,True,f'htr{i}{j}{k}b')
            edge(hi,y,affine(),0,True,f'htr{i}{j}{k}c')
        for i in DEFECTS:
            ds=[f'd{a}{b}' for a,b in self.rows[i]]
            for k in range(5):
                score=f's{i}{k}';positive=values[score]>0;phase=(score,'positive' if positive else 'zero')
                s=affine(score)
                if self.min_domain:
                    u=affine(f'u{i}{k}')
                    if k<4:
                        left=f't{i}' if k==0 else ds[k-1];right=ds[k]
                        edge(right,left,affine(),0,False,f'hnonneg{i}{k}')
                        edge(right,left,(s+u).scale(-1),0,False,f'hgap{i}{k}b')
                        edge(left,right,s+affine(c=2),0,True,f'hgap{i}{k}c')
                    else:
                        edge(f't{i}',ds[-1],n,1,False,f'hnonneg{i}{k}')
                        edge(f't{i}',ds[-1],n+(s+u).scale(-1),1,False,f'hgap{i}{k}b')
                        edge(ds[-1],f't{i}',s+n.scale(-1)+affine(c=2),-1,True,f'hgap{i}{k}c')
                    continue
                if k<4:
                    left=f't{i}' if k==0 else ds[k-1];right=ds[k]
                    edge(right,left,affine(),0,False,f'hnonneg{i}{k}')
                    if positive:
                        edge(right,left,s.scale(-1)+affine(c=-1),0,False,f'hgap{i}{k}b',phase)
                        edge(left,right,s+affine(c=2),0,True,f'hgap{i}{k}c',phase)
                    else:edge(left,right,affine(c=2),0,True,f'hgap{i}{k}b',phase)
                else:
                    edge(f't{i}',ds[-1],n,1,False,f'hnonneg{i}{k}')
                    if positive:
                        edge(f't{i}',ds[-1],n+s.scale(-1)+affine(c=-1),1,False,f'hgap{i}{k}b',phase)
                        edge(ds[-1],f't{i}',s+n.scale(-1)+affine(c=2),-1,True,f'hgap{i}{k}c',phase)
                    else:edge(ds[-1],f't{i}',n.scale(-1)+affine(c=2),-1,True,f'hgap{i}{k}b',phase)
        return arcs

    def negative_cycle(self,arcs,values,delta):
        self.stats['dbm_runs']+=1
        # A formal infinitesimal count preserves zero-cost strict cycles through
        # repeated Bellman-Ford relaxation.  No numeric epsilon is introduced.
        size=len(self.vertices);distance=[(Fraction(0),0)]*size;pred=[None]*size;last=None
        def less(a,b):return a[0]<b[0] or (a[0]==b[0] and a[1]<b[1])
        weights=[(Fraction(arc.a.evaluate(values))+arc.b*delta,-int(arc.strict)) for arc in arcs]
        for _ in range(size):
            last=None
            for index,arc in enumerate(arcs):
                origin=distance[arc.source];weight=weights[index]
                candidate=(origin[0]+weight[0],origin[1]+weight[1])
                if less(candidate,distance[arc.target]):distance[arc.target]=candidate;pred[arc.target]=index;last=arc.target
            if last is None:return None
        cursor=last
        for _ in range(size):cursor=arcs[pred[cursor]].source
        initial=cursor;ids=[]
        while True:
            index=pred[cursor];ids.append(index);cursor=arcs[index].source
            if cursor==initial:break
            assert len(ids)<=size
        a=affine();b=0;strict=False
        for index in ids:a=a+arcs[index].a;b+=arcs[index].b;strict=strict or arcs[index].strict
        cost=Fraction(a.evaluate(values))+b*delta
        assert cost<0 or(cost==0 and strict),(cost,ids)
        self.stats['cycles']+=1
        return Cycle(a,b,strict,tuple(ids))

    def separate(self,values):
        arcs=self.geometry(values)
        lower=(Fraction(1,2),False,Cycle(affine(c=-1),2,False,(),'hdelta0'))
        upper=(Fraction(1),True,Cycle(affine(c=1),-1,True,(),'hdelta1'))
        for _ in range(200):
            if lower[0]>upper[0] or(lower[0]==upper[0] and(lower[1] or upper[1])):
                pos,neg=lower[2],upper[2]
                result=pos.a.scale(-neg.b)+neg.a.scale(pos.b)
                return {'A':result,'strict':pos.strict or neg.strict,'cycles':[pos,neg],'arcs':arcs}
            delta=(lower[0]+upper[0])/2
            cycle=self.negative_cycle(arcs,values,delta)
            if cycle is None:return {'geometry_sat_delta':str(delta),'arcs':arcs}
            if cycle.b==0:return {'A':cycle.a,'strict':cycle.strict,'cycles':[cycle],'arcs':arcs}
            bound=Fraction(-cycle.a.evaluate(values),cycle.b)
            if cycle.b>0:
                assert bound>lower[0] or(bound==lower[0] and cycle.strict)
                lower=(bound,cycle.strict,cycle)
            else:
                assert bound<upper[0] or(bound==upper[0] and cycle.strict)
                upper=(bound,cycle.strict,cycle)
        raise RuntimeError('parametric cycle separation budget exhausted')

    def fingerprint(self):
        zero={name:0 for name in NAMES};positive={name:1 for name in NAMES}
        payload={'schema':'symbolic-cycle-score-v3','mask':self.mask,'upper':self.upper,'rows':self.rows,'min_domain':self.min_domain,
                 'base':{name:value.sexpr() for name,value in self.base.items()},'vertices':self.vertices,
                 'names':NAMES,'floor_domains':'score=0:0<=g<2; score>=1:score+1<=g<score+2',
                 'delta_domain':'1/2<=delta<1','full_triangle_order':TRIPLES,
                 'complete_zero_arc_templates':[arc.serial() for arc in self.geometry(zero)],
                 'complete_positive_arc_templates':[arc.serial() for arc in self.geometry(positive)],
                 'preorders':self.orders}
        return hashlib.sha256(json.dumps(payload,sort_keys=True,separators=(',',':')).encode()).hexdigest()

    def run(self,wall,max_cuts):
        started=time.monotonic()
        while time.monotonic()-started<wall and len(self.cuts)<max_cuts:
            status=self.master.check()
            if status==z3.unknown:return {'status':'UNKNOWN','reason':self.master.reason_unknown()}
            if status==z3.unsat:return {'status':'UNSAT_INTEGER_MASTER','core':[str(name) for name in self.master.unsat_core()]}
            model=self.master.model();values={name:model.eval(value,model_completion=True).as_long() for name,value in self.variables.items()}
            self.stats['candidates']+=1
            result=self.separate(values)
            if 'geometry_sat_delta' in result:return {'status':'SAT_NECESSARY_GEOMETRY_ONLY','candidate':values,'delta':result['geometry_sat_delta']}
            ids=sorted({index for cycle in result['cycles'] for index in cycle.arc_ids})
            phases=sorted({result['arcs'][index].phase for index in ids if result['arcs'][index].phase is not None})
            threshold=1 if result['strict'] else 0
            cut=result['A'].z3(self.variables)>=threshold
            hypotheses=[self.variables[name]>=1 if arm=='positive' else self.variables[name]==0 for name,arm in phases]
            clause=z3.Implies(z3.And(*hypotheses),cut)
            assert not z3.is_true(z3.simplify(z3.substitute(clause,*[(self.variables[name],z3.IntVal(value)) for name,value in values.items()])))
            name=f'hcut{len(self.cuts)}'
            self.master.assert_and_track(clause,z3.Bool(name))
            serial={'name':name,'A':result['A'].serial(),'threshold':threshold,'phases':phases,
                    'cycles':[cycle.serial() for cycle in result['cycles']],
                    'arcs':{str(index):result['arcs'][index].serial() for index in ids},
                    'integer_clause':clause.sexpr(),'candidate':values}
            self.cuts.append(serial);self.stats['learned_cuts']+=1
        return {'status':'BUDGET_STOP'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mask',type=int,default=0)
    parser.add_argument('--upper',type=int)
    parser.add_argument('--wall-seconds',type=float,default=20)
    parser.add_argument('--max-cuts',type=int,default=300)
    parser.add_argument('--preorders',action='store_true')
    parser.add_argument('--min-domain',action='store_true')
    parser.add_argument('--emit-min-probe',action='store_true')
    args=parser.parse_args();started=time.monotonic()
    if args.min_domain:
        NAMES.extend(f'u{i}{k}' for i in DEFECTS for k in range(5));INDEX.update({name:index for index,name in enumerate(NAMES)})
    if args.emit_min_probe:
        assert args.min_domain
        emit_min_probe(args.mask);return
    probe=Probe(args.mask,args.upper,args.preorders,args.min_domain)
    result=probe.run(args.wall_seconds,args.max_cuts)
    report={'mask':args.mask,'n_lower':4,'n_upper':args.upper,'min_domain':args.min_domain,'result':result,'stats':probe.stats,
            'seconds':time.monotonic()-started,'fingerprint_sha256':probe.fingerprint(),
            'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'kernel':'NOT_RUN','solver_seed':0,'cuts':probe.cuts,'preorders':probe.orders,
            'scope':'Fixed-orientation necessary ModelSix integer-score diagnostic only; not an original-point counterexample or trusted proof.'}
    path=ROOT/f'research/JSP404_SIX_SYMBOLIC_CYCLES_M{args.mask}_B{args.upper or "UNBOUNDED"}{"_MIN" if args.min_domain else ""}{"_ORDERS" if args.preorders else ""}_20261005.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({key:value for key,value in report.items() if key!='cuts'}),flush=True)


def emit_min_probe(mask):
    """Ordinary typed ModelSix source.  Neither the master nor cuts are trusted."""
    import export_four_row_certificate_20261004 as old
    report=json.loads((ROOT/f'research/JSP404_SIX_SYMBOLIC_CYCLES_M{mask}_BUNBOUNDED_MIN_20261005.json').read_text())
    selected=json.loads((ROOT/f'research/JSP404_SIX_SYMBOLIC_CYCLES_M{mask}_MIN_CORE_20261005.json').read_text())['selected_cut_names']
    rows=row_orders(mask)
    def chord(edge):return f'M.d {edge[0]} {edge[1]}'
    def ls(edges):return '['+', '.join(chord(edge) for edge in edges)+']'
    def gaps(i):
        ds=[chord(edge) for edge in rows[i]]
        return [f'({ds[0]} - M.theta {i})']+[f'({ds[k+1]} - {ds[k]})' for k in range(3)]+[f'(M.theta {i} + ((n : ℝ) + M.delta) - {ds[3]})']
    lines=['import Jsp000404.SixExactFloorKernelSymbolicInterval',
           f'import Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}Integer','',
           '/-! Unbounded-n fixed-orientation prototype. Every integer cut is derived',
           'from actual ModelSix gap facts before the ordinary omega closure. -/',
           'namespace Jsp404.SixExactFloorKernel','',
           'set_option maxHeartbeats 16000000 in',
           f'theorem symbolic_mask{mask}_probe {{n : ℕ}} (M : SixModelCompression.ModelSix n)',
           '    (hn4 : 4 ≤ n) (hhigh : (1/2 : ℝ) ≤ M.delta)']
    lines += [f'    (hdef{i} : SixModelCompression.rowDefect M {i} = {c})' for i,c in DEFECTS.items()]
    for bit,(i,j,k) in enumerate(TRIPLES):
        x,y,z=chord((i,j)),chord((i,k)),chord((j,k));lo,hi=(z,x) if mask>>bit&1 else(x,z)
        lines += [f'    (htri{i}{j}{k} : {lo}+1 ≤ {hi} ∧ {lo} < {y} ∧ {y} < {hi})']
    lines += ['    : False := by','  have hdelta0 := hhigh','  have hdelta1 := M.hdelta.2']
    for i in range(5):
        lines += [f'  obtain ⟨ht{i}a, ht{i}b⟩ := M.theta_bounds {i}']
        if i<4:lines += [f'  have ht{i}{i+1} := M.htheta (show ({i} : Fin 5) < {i+1} from by decide)']
    for i,j in EDGES:lines += [f'  obtain ⟨hc{i}{j}a, hc{i}{j}b⟩ := M.corridor {i} {j} (by decide)']
    for i,j,k in TRIPLES:lines += [f'  obtain ⟨htr{i}{j}{k}a, htr{i}{j}{k}b, htr{i}{j}{k}c⟩ := htri{i}{j}{k}']
    for i,c in DEFECTS.items():
        raw=[tuple(sorted((i,j))) for j in range(5) if i!=j];es=rows[i];gs=gaps(i);ss=[f's{i}{k}' for k in range(5)]
        lines += [f'  have hsort{i} : ({ls(es)} : List ℝ).Pairwise (· ≤ ·) := by',
                  '    simp [List.pairwise_cons]','    repeat\' apply And.intro','    all_goals linarith',
                  f'  have hp{i} := M.row_perm {i}']
        syms=[]
        for j in range(i):
            syms.append(f'hcanon{i}{j}')
            lines += [f'  have hcanon{i}{j} : M.d {i} {j} = M.d {j} {i} := M.symm {i} {j} (by decide)']
        lines += [f'  have he{i} : (((List.finRange 5).erase ({i} : Fin 5)).map (M.d {i})) = {ls(raw)} := by',
                  '    norm_num [List.finRange, List.ofFn_succ'+(', '+', '.join(syms) if syms else '')+']',
                  f'  rw [he{i}] at hp{i}',f'  have hperm{i} := hp{i}.trans ({old.permutation_term(raw,es)})',
                  f'  have hrow{i} : M.rowxs {i} = {ls(es)} := hperm{i}.eq_of_pairwise\' (M.row_sorted {i}) hsort{i}',
                  f'  have hrow_nonneg{i} := SmallScoreGapBounds.model_gaps_nonneg M {i}',
                  f'  simp only [SmallScoreGapBounds.modelGaps, hrow{i}, StrongGapBudget.linearGaps] at hrow_nonneg{i}']
        for k,(g,s) in enumerate(zip(gs,ss)):
            lines += [f'  let {s} : ℕ := ⌊{g}⌋₊ - 1',f'  let u{i}{k} : ℕ := min {s} 1',
                      f'  have hnonneg{i}{k} : 0 ≤ {g} := hrow_nonneg{i} {g} (by simp)',
                      f'  obtain ⟨hgap{i}{k}b, hgap{i}{k}c⟩ := score_gap_min_interval {g} hnonneg{i}{k}',
                      f'  change ({s} : ℝ) + (u{i}{k} : ℝ) ≤ {g} at hgap{i}{k}b',
                      f'  change {g} < ({s} : ℝ) + 2 at hgap{i}{k}c']
        nat_sum=ss[-1]
        for s in reversed(ss[:-1]):nat_sum=f'{s} + ({nat_sum})'
        nat_sum_zero=f'{ss[0]} + ({ss[1]} + ({ss[2]} + ({ss[3]} + ({ss[4]} + 0))))'
        lines += [f'  have hsum_nat{i} : ({nat_sum}) + {c} = n := by',
                  f'    have h := SmallScoreGapBounds.model_score M {i} {c} hdef{i}',
                  f'    simp only [SmallScoreGapBounds.modelGaps, hrow{i}, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h',
                  f'    change ({nat_sum_zero}) + {c} = n at h','    omega']
    lookup={cut['name']:cut for cut in report['cuts']}
    def poly(terms,constant):
        entries=[name if coeff==1 else f'{coeff} * {name}' for name,coeff in terms]
        if constant:entries.append(str(constant))
        return '('+' + '.join(entries or ['0'])+')'
    integer_goals=[]
    for name in selected:
        cut=lookup[name];assert not cut['phases']
        a=cut['A'];p=poly([(n,c) for n,c in a['coefficients'].items() if c>0],max(a['constant'],0))
        q=poly([(n,-c) for n,c in a['coefficients'].items() if c<0],max(-a['constant'],0))
        facts=list(dict.fromkeys(arc['premise'] for arc in cut['arcs'].values()))
        facts += [cycle['range_premise'] for cycle in cut['cycles'] if cycle['range_premise']]
        strict=cut['threshold']==1;op='<' if strict else '≤'
        goal=f'{q} + 1 ≤ {p}' if strict else f'{q} ≤ {p}'
        integer_goals.append((name,goal))
        lines += [f'  have {name} : {goal} := by',
                  f'    have hreal : (({q} : ℕ) : ℝ) {op} (({p} : ℕ) : ℝ) := by',
                  '      push_cast',f'      linarith only [{", ".join(facts)}]']
        if strict:lines += [f'    have hnat : {q} < {p} := by exact_mod_cast hreal','    omega']
        else:lines += ['    exact_mod_cast hreal']
    arguments=NAMES+['hn4']+[f'hsum_nat{i}' for i in DEFECTS]+selected+['(by rfl)' for i in DEFECTS for k in range(5)]
    lines += [f'  exact symbolic_mask{mask}_integer_closure '+' '.join(arguments),
              f'\n#print axioms symbolic_mask{mask}_probe','end Jsp404.SixExactFloorKernel']
    text='\n'.join(lines)+'\n';path=ROOT/f'Jsp000404/SixExactFloorKernelSymbolicMask{mask:03d}Probe.lean';path.write_text(text)
    print(json.dumps({'source':str(path),'lines':len(text.splitlines()),'bytes':len(text.encode()),
                      'cuts':len(selected),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'kernel':'NOT_RUN'}))
    # Integer closure is produced separately by the adaptive shard exporter.
    # Never overwrite its checked wrapper with a global-min omega experiment.

if __name__=='__main__':main()
