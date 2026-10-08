#!/usr/bin/env python3
"""SOURCE_ONLY single joint GenericModel6 4 R1 probe; no word/profile enumeration.

Run only after explicit budget authorization. Exactly one solver worker;
heavy rank0, all six full rows and all20 triangle alternatives are encoded.
A positive result must pass the independent stdlib Fraction verifier.
Scalar SAT is not planar realizability or the original minimal Model.
"""
from pathlib import Path
from itertools import combinations
import hashlib,json,os,signal,subprocess,sys,time,resource
ROOT=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()


def worker(out):
    import z3
    from verify_n4_r1_positive_seven_scalar_20261008 import verify
    resource.setrlimit(resource.RLIMIT_CPU,(105,105))
    solver=z3.SolverFor('QF_LIRA');solver.set(timeout=95000,random_seed=0)
    delta=z3.Real('delta');theta=[z3.Real(f'theta{i}') for i in range(6)]
    edges=list(combinations(range(6),2));d={e:z3.Real(f'd{e[0]}{e[1]}') for e in edges}
    chord=lambda i,j:d[tuple(sorted((i,j)))]
    solver.add(delta>=z3.RealVal('1/2'),delta<1,theta[0]==0)
    for i,t in enumerate(theta):
        solver.add(t>=0,t<=delta)
        if i<5:solver.add(t<theta[i+1])
    for (i,j),x in d.items():solver.add(theta[i]+1<=x,x<=3+delta+theta[j])
    arms=[]
    for i,j,k in combinations(range(6),3):
        x,y,z=chord(i,j),chord(i,k),chord(j,k)
        low=z3.And(x+1<=z,x<y,y<z);high=z3.And(z+1<=x,z<y,y<x)
        solver.add(z3.Or(low,high));arms.append(high)
    xsrows=[];gaprows=[];qrows=[]
    for i in range(6):
        xs=[chord(i,j) for j in range(6) if j!=i]
        # Fixed five-entry bubble sorting network: ten comparator swaps.
        for end in range(4,0,-1):
            for a in range(end):
                x,y=xs[a],xs[a+1]
                xs[a],xs[a+1]=z3.If(x<=y,x,y),z3.If(x<=y,y,x)
        gs=[xs[0]-theta[i]]+[b-a for a,b in zip(xs,xs[1:])]+[theta[i]+4+delta-xs[-1]]
        qs=[z3.Int(f'q{i}_{k}') for k in range(6)]
        for g,q in zip(gs,qs):solver.add(g>=0,q>=0,q<=4,q<=g,g<q+1)
        solver.add(z3.Sum([z3.If(q>=1,q-1,0) for q in qs])==(2 if i==0 else 1))
        xsrows.append(xs);gaprows.append(gs);qrows.append(qs)
    (out/'problem.smt2').write_text(solver.sexpr())
    begin=time.monotonic();status=solver.check()
    record={'status':str(status),'solver_seconds':time.monotonic()-begin,'m':6,'n':4,'heavy':0,
            'theta_gauge':0,'delta_range':'1/2<=delta<1','triangles':20,'corridors':15,
            'full_rows':6,'exact_gap_floors':36,'physical_realizability':'NOT_CLAIMED',
            'original_minimal_model_caps':'NOT_CHECKED','Lean_proof':False}
    if status==z3.sat:
        model=solver.model()
        (out/'solver-model.raw.smt2').write_text(model.sexpr())
        def qstr(e):
            x=model.eval(e,model_completion=True)
            if z3.is_int_value(x):return str(x.as_long())
            if not z3.is_rational_value(x):raise ValueError('Non-rational model value')
            return str(x.numerator_as_long())+'/'+str(x.denominator_as_long())
        raw={'n':4,'heavy':0,'delta':qstr(delta),'theta':[qstr(x) for x in theta],
             'd':{f'{i},{j}':qstr(x) for (i,j),x in d.items()},
             'word_bits':[int(z3.is_true(model.eval(a))) for a in arms],
             'rowxs':[[qstr(x) for x in row] for row in xsrows],
             'gaps':[[qstr(x) for x in row] for row in gaprows],
             'floors':[[model.eval(q,model_completion=True).as_long() for q in row] for row in qrows]}
        (out/'candidate.raw.json').write_text(json.dumps(raw,indent=2)+'\n')
        checked=verify(raw);(out/'candidate.verified.json').write_text(json.dumps(checked,indent=2)+'\n')
        record['status']='SAT_EXACT_RATIONAL_GENERICMODEL6_PROFILE'
        record['candidate_sha256']=sha(out/'candidate.raw.json')
        record['verified_sha256']=sha(out/'candidate.verified.json')
    elif status==z3.unknown:record['reason']=solver.reason_unknown()
    else:record['interpretation']='UNSAT solver diagnostic only, not a Lean proof'
    (out/'result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True)


def main():
    if len(sys.argv)==3 and sys.argv[1]=='--worker':return worker(Path(sys.argv[2]))
    if len(sys.argv)!=3 or sys.argv[1]!='--out':raise SystemExit('usage: probe_n4_r1_positive_seven_scalar_20261008.py --out NEW_DIRECTORY')
    out=Path(sys.argv[2]).resolve();out.mkdir(parents=True,exist_ok=False)
    for name in ('probe_n4_r1_positive_seven_scalar_20261008.py','verify_n4_r1_positive_seven_scalar_20261008.py'):
        (out/name).write_bytes((ROOT/'tools'/name).read_bytes())
    sys.path.insert(0,str(ROOT/'tools'))
    from check_six_symbolic_kernel_20261005 import rss_tree
    start=time.monotonic();peak=0;stop=None
    with (out/'worker.raw.log').open('w') as log:
        proc=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'--worker',str(out)],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        while proc.poll() is None:
            rss,_,_=rss_tree(proc.pid)
            own=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            own_kib=own//1024 if sys.platform=='darwin' else own
            peak=max(peak,rss+own_kib)
            if peak>=512*1024 or time.monotonic()-start>=110:
                stop='RSS_512_MIB' if peak>=512*1024 else 'WALL_110_S_RESERVED_GRACE'
                os.killpg(proc.pid,signal.SIGTERM);break
            time.sleep(.1)
        try:proc.wait(timeout=5)
        except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait();stop=stop or 'TERMINATION_GRACE'
    receipt={'exit_code':proc.returncode,'resource_stop':stop,'wall_seconds':time.monotonic()-start,
             'peak_worker_tree_plus_controller_kib':peak,'wall_budget_seconds':120,'rss_budget_mib':512,
             'solver_runs':1,'word_or_profile_outer_enumeration':False,'Lean_run':False}
    (out/'resource-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
    if stop or proc.returncode:raise SystemExit(1)


if __name__=='__main__':main()
