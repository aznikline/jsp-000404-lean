#!/usr/bin/env python3
"""Exact necessary-angle diagnostic; outputs are not Lean certificates.

Choose a generic projection and order actual points by it. Every unordered
chord is lifted to (0, P) in the common upper half-plane, where P=pi/lambda.
For i<j<k, y=d_ik lies strictly between x=d_ij and z=d_jk. The middle
vertex angle is P-|z-x|, and the endpoint angles are |y-x|,|z-y|.
ALL THREE triangle caps are encoded below. The older weak diagnostic
omitted the two endpoint caps and cannot falsify this exact model.

A positive row requires its projective directions to fit an arc of length
P-2, beginning at one occupied ray. This deliberately allows score two:
there are no no-saturation, zero-row, deletion, minimality or length
hypotheses in positive_only mode. SAT is not a point realization.
"""
import argparse
from fractions import Fraction
import itertools,json,time
from pathlib import Path
import z3

ROOT=Path(__file__).resolve().parents[1]

def build(s,positive,band,mode='positive_only'):
    P=z3.Real('period')
    d={(i,j):z3.Real(f'd_{i}_{j}') for i,j in itertools.combinations(range(s),2)}
    get=lambda i,j:d[tuple(sorted((i,j)))]
    C={'period':z3.And(P>=3,P<(z3.RealVal('7/2') if band=='LOW' else 4))}
    if band=='HIGH':C['period']=z3.And(C['period'],P>=z3.RealVal('7/2'))
    for ij,x in d.items():C[f'range_{ij[0]}_{ij[1]}']=z3.And(0<x,x<P)
    for i,j,k in itertools.combinations(range(s),3):
        x,y,z=get(i,j),get(i,k),get(j,k)
        ascending=z3.And(x+1<=z,x<y,y<z)
        descending=z3.And(z+1<=x,z<y,y<x)
        if mode!='weak_missing_endpoint_caps':
            ascending=z3.And(ascending,y-x<=P-1,z-y<=P-1)
            descending=z3.And(descending,y-z<=P-1,x-y<=P-1)
        C[f'triangle_{i}_{j}_{k}']=z3.Or(ascending,descending)
    for i in positive:
        xs=[get(i,j) for j in range(s) if j!=i]
        C[f'positive_{i}']=z3.Or(*[z3.And(*[z3.Or(z3.And(x<=y,y-x<=P-2),z3.And(y<x,y+P-x<=P-2)) for y in xs]) for x in xs])
    return P,d,C

def check(s,positive,band,timeout_ms=5000,mode='positive_only',include_core=False):
    P,d,C=build(s,positive,band,mode)
    solver=z3.SolverFor('QF_LRA');solver.set(timeout=timeout_ms,random_seed=0)
    for k,v in C.items():solver.assert_and_track(v,z3.Bool(k))
    st=time.monotonic();status=solver.check()
    rec={'band':band,'s':s,'positive_indices':list(positive),'nonpositive_unconstrained_indices':[i for i in range(s) if i not in positive],
         'mode':mode,'status':str(status),'seconds':round(time.monotonic()-st,4),'timeout_ms':timeout_ms,'conditions_count':len(C)}
    if status==z3.unsat:
        rec['unsat_core_names']=[str(x) for x in solver.unsat_core()]
        if include_core:rec['unsat_core_conditions']={k:C[k].sexpr() for k in rec['unsat_core_names']}
    elif status==z3.unknown:rec['reason']=solver.reason_unknown()
    else:
        M=solver.model()
        def val(x):
            q=M.eval(x,model_completion=True);return Fraction(q.numerator_as_long(),q.denominator_as_long())
        p=val(P);dv={ij:val(x) for ij,x in d.items()};g=lambda i,j:dv[tuple(sorted((i,j)))]
        checks={'period':3<=p<(Fraction(7,2) if band=='LOW' else 4) and (band=='LOW' or p>=Fraction(7,2)),
                'ranges':all(0<x<p for x in dv.values()),
                'ordered_triangles':all(((g(i,j)+1<=g(j,k) and g(i,j)<g(i,k)<g(j,k) and (mode=='weak_missing_endpoint_caps' or(g(i,k)-g(i,j)<=p-1 and g(j,k)-g(i,k)<=p-1))) or (g(j,k)+1<=g(i,j) and g(j,k)<g(i,k)<g(i,j) and (mode=='weak_missing_endpoint_caps' or(g(i,k)-g(j,k)<=p-1 and g(i,j)-g(i,k)<=p-1)))) for i,j,k in itertools.combinations(range(s),3)),
                'positive_windows':all(any(all((y-x if x<=y else y+p-x)<=p-2 for y in [g(i,j) for j in range(s) if j!=i]) for x in [g(i,j) for j in range(s) if j!=i]) for i in positive)}
        assert all(checks.values()),checks
        rec['angular_model']={'period':str(p),'chords':{f'{i},{j}':str(x) for (i,j),x in dv.items()},'validated_exactly_with_Fraction':True,'checks':checks,'point_realizability':'NOT_CHECKED'}
    return rec

def reflection_representatives(s,r):
    for pos in itertools.combinations(range(s),r):
        mirror=tuple(sorted(s-1-i for i in pos))
        if pos<=mirror:yield pos

def main():
    A=argparse.ArgumentParser();A.add_argument('--all',action='store_true');A.add_argument('--timeout-ms',type=int,default=5000);A.add_argument('--wall-seconds',type=float,default=180);args=A.parse_args()
    report={'diagnostic_only':True,'no_Lean_certificate':True,'mode':'positive_only','definitions_source':'tools/check_n3_nosat_ordered_20261004.py','cases':[],'unvisited':[]}
    if args.all:plan=[(band,cap+1-r,pos) for band,cap,rmax in [('LOW',8,4),('HIGH',10,5)] for r in range(rmax,-1,-1) for pos in reflection_representatives(cap+1-r,r)]
    else:plan=[(band,s,pos) for band,s,r in [('LOW',5,4),('HIGH',6,5)] for pos in reflection_representatives(s,r)]
    st=time.monotonic()
    for k,(band,s,pos) in enumerate(plan):
        remaining=args.wall_seconds-(time.monotonic()-st)
        if remaining<=0:report['unvisited']=[{'band':b,'s':n,'positive_indices':list(p)} for b,n,p in plan[k:]];break
        rec=check(s,pos,band,min(args.timeout_ms,max(1,int(remaining*1000))),include_core=not args.all)
        print(json.dumps({k:v for k,v in rec.items() if k not in ['unsat_core_conditions','angular_model']}),flush=True);report['cases'].append(rec)
    report['elapsed_seconds']=round(time.monotonic()-st,3)
    out='JSP404_N3_NOSAT_ORDERED_ALL_DIAGNOSTIC_20261004.json' if args.all else 'JSP404_N3_NOSAT_ORDERED_POSITIVE_DIAGNOSTIC_20261004.json'
    (ROOT/'research'/out).write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
