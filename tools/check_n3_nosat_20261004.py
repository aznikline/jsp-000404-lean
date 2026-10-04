#!/usr/bin/env python3
"""Shared projective chord necessary-condition diagnostics, never a Lean proof.
Period is pi/lambda; every triple has its three projective-edge circular
intervals at most period-1. Rows and every zero-victim deletion have exact
score zero or one. No point realizability is claimed.
"""
import itertools, json, time
from pathlib import Path
from fractions import Fraction
import z3

def sorted_expr(xs):
    xs=list(xs)
    for k in range(1,len(xs)):
        for j in range(k,0,-1):
            x,y=xs[j-1:j+1]
            xs[j-1],xs[j]=z3.If(x<=y,x,y),z3.If(x<=y,y,x)
    return xs

def gaps(P,xs):
    xs=sorted_expr(xs)
    return [b-a for a,b in zip(xs,xs[1:])]+[P+xs[0]-xs[-1]]

def score_cond(gs,k):
    if k==0: return z3.And(*[z3.And(g>=0,g<2) for g in gs])
    return z3.Or(*[z3.And(*[z3.And(g>=2,g<3) if h==j else z3.And(g>=0,g<2) for h,g in enumerate(gs)]) for j in range(len(gs))])

def validate(P,d,s,r,band):
    get=lambda i,j:d[tuple(sorted((i,j)))]
    def fg(xs):
        xs=sorted(xs)
        return [b-a for a,b in zip(xs,xs[1:])]+[P+xs[0]-xs[-1]]
    def score(gs):return sum(max(g.numerator//g.denominator-1,0) for g in gs)
    checks={"strip":3<=P<(Fraction(7,2) if band=="LOW" else 4) and (band=="LOW" or P>=Fraction(7,2)),
            "chord_range":all(0<=v<P for v in d.values()),
            "triangle_projective_intervals":all(all(0<g<=P-1 for g in fg([get(i,j),get(i,k),get(j,k)])) for i,j,k in itertools.combinations(range(s),3)),
            "original_scores":all(score(fg([get(i,j) for j in range(s) if j!=i]))==int(i<r) for i in range(s)),
            "zero_deletions_preserve_all_scores":all(score(fg([get(i,j) for j in range(s) if j!=i and j!=q]))==int(i<r) for q in range(r,s) for i in range(s) if i!=q)}
    assert all(checks.values()),checks
    return {"validated_exactly_with_Fraction":True,"checks":checks,"point_realizability":"NOT_CHECKED"}

def run(s,r,band,timeout=3000):
    P=z3.Real('period')
    d={(i,j):z3.Real(f'd_{i}_{j}') for i,j in itertools.combinations(range(s),2)}
    get=lambda i,j:d[tuple(sorted((i,j)))]
    S=z3.SolverFor('QF_LRA'); S.set(timeout=timeout,random_seed=0)
    S.add(P>=3,P<z3.RealVal('7/2') if band=='LOW' else P<4)
    if band=='HIGH':S.add(P>=z3.RealVal('7/2'))
    for x in d.values():S.add(x>=0,x<P)
    # Rotate at a score-one row and label its rays in sorted projective order.
    if r:
        S.add(get(0,1)==0)
        for j in range(1,s-1):S.add(get(0,j)<get(0,j+1))
        S.add(get(0,s-1)<=P-2)
    else:S.add(get(0,1)==0)
    for i,j,k in itertools.combinations(range(s),3):
        gs=gaps(P,[get(i,j),get(i,k),get(j,k)])
        S.add(*[z3.And(g>0,g<=P-1) for g in gs])
    for i in range(s):S.add(score_cond(gaps(P,[get(i,j) for j in range(s) if j!=i]),int(i<r)))
    for q in range(r,s):
        for i in range(s):
            if i!=q:S.add(score_cond(gaps(P,[get(i,j) for j in range(s) if j!=i and j!=q]),int(i<r)))
    st=time.monotonic(); ans=S.check()
    rec={'band':band,'s':s,'r':r,'F':s+r,'status':str(ans),'seconds':round(time.monotonic()-st,3),'timeout_ms':timeout}
    if ans==z3.sat:
        M=S.model()
        def val(x):
            q=M.eval(x,model_completion=True)
            return Fraction(q.numerator_as_long(),q.denominator_as_long())
        pv=val(P); dv={ij:val(x) for ij,x in d.items()}
        rec['angular_model']={'period':str(pv),'chords':{f'{i},{j}':str(x) for (i,j),x in dv.items()},'actual_point_realizability':'NOT_CHECKED','validation':validate(pv,dv,s,r,band)}
    elif ans==z3.unknown:rec['reason']=S.reason_unknown()
    return rec
if __name__=='__main__':
    report={'diagnostic_only':True,'no_Lean_proof':True,'scope':'Necessary projective intervals only; normalization selects one angular order subcase, not all geometric profiles. SAT is not an actual counterexample.','cases':[]}
    for band,cap,rmax in [('LOW',8,4),('HIGH',10,5)]:
        for r in range(rmax,-1,-1):
            rec=run(cap+1-r,r,band)
            print(json.dumps(rec),flush=True);report['cases'].append(rec)
    Path('research/JSP404_N3_NOSAT_DIAGNOSTIC_20261004.json').write_text(json.dumps(report,indent=2)+'\n')
