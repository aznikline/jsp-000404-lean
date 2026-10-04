"""Bounded diagnostic for the exact four-row necessary-model core.

UNSAT here is not a Lean certificate and does not assert planar realization.
Each ten-triangle orientation is fixed first, making each four-chord row order
explicit; only rows (0,1,3,4) receive defect equations (2,3,3,2).
"""
import itertools
import json
from pathlib import Path
import time
import z3
from collections import Counter
tri=list(itertools.combinations(range(5),3));edges=list(itertools.combinations(range(5),2))
def orientations():
 out=[]
 for mask in range(1024):
  adj={e:set() for e in edges}
  for t,(a,b,c) in enumerate(tri):
   x=(a,b);y=(a,c);z=(b,c)
   a1,b1,c1=(x,y,z) if ((mask>>t)&1)==0 else (z,y,x)
   adj[a1].add(b1);adj[b1].add(c1)
  clos={e:set(es) for e,es in adj.items()}
  changed=True
  while changed:
   changed=False
   for a in edges:
    new=set(clos[a])
    for b in list(clos[a]):new |= clos[b]
    if new != clos[a]:clos[a]=new;changed=True
  if any(e in clos[e] for e in edges):continue
  row=[]
  for i in range(5):
   es=[tuple(sorted((i,j))) for j in range(5) if i!=j]
   old=tuple(es)
   es.sort(key=lambda a:sum(a in clos[b] for b in old))
   if any(es[b] not in clos[es[a]] for a in range(4) for b in range(a+1,4)):raise AssertionError
   row.append(es)
  out.append((mask,row))
 return out

def build_oriented(nval,defs,mask,row):
 s=z3.Solver();s.set(timeout=3000)
 n=z3.Int('n') if nval is None else nval
 if nval is None:s.add(n>=3,n<=24)
 de=z3.Real('de');th=[z3.Real('t'+str(i)) for i in range(5)]
 d={e:z3.Real('d'+''.join(map(str,e))) for e in edges}
 s.add(de>=z3.RealVal('1/2'),de<1)
 for t in th:s.add(t>=0,t<=de)
 for i in range(4):s.add(th[i]<th[i+1])
 for (i,j),x in d.items():s.add(th[i]+1<=x,x<=n+de-1+th[j])
 for t,(a,b,c) in enumerate(tri):
  x,y,z=d[a,b],d[a,c],d[b,c]
  if (mask>>t)&1:s.add(z+1<=x,z<y,y<x)
  else:s.add(x+1<=z,x<y,y<z)
 for i,c in defs.items():
  xs=[d[e] for e in row[i]]
  gs=[xs[0]-th[i]]+[xs[k+1]-xs[k] for k in range(3)]+[th[i]+n+de-xs[-1]]
  qs=[z3.Int(f'q{i}{k}') for k in range(5)]
  for g,q in zip(gs,qs):s.add(g>=0,q>=0,q<=n,q<=g,g<q+1)
  s.add(z3.Sum([z3.If(q>=1,q-1,0) for q in qs])==n-c)
  s.add(z3.Sum([z3.If(q>=1,1,0) for q in qs])<=c)
 return s
if __name__=='__main__':
 opts=orientations();print('orientations',len(opts),flush=True)
 defs={0:2,1:3,3:3,4:2};rec=[];st=time.monotonic()
 for mask,row in opts:
  s=build_oriented(None,defs,mask,row);tt=time.monotonic();r=s.check()
  rowrec={'mask':mask,'status':str(r),'seconds':time.monotonic()-tt}
  rec.append(rowrec);print(json.dumps(rowrec),flush=True)
 print('total',time.monotonic()-st,Counter(x['status'] for x in rec),flush=True)
 report={'date':'2026-10-04','solver':z3.get_version_string(),
   'scope':'Necessary scalar ModelSix constraints only; no planar realization claim',
   'model_source':'Jsp000404/SixModelCompression.lean',
   'n_range':'integer 3..24, inclusive', 'delta_range':'1/2 <= delta < 1',
   'constrained_row_defects':{str(i):v for i,v in defs.items()},
   'unconstrained_row':2, 'deep_defect_constraint':None,
   'orientation_count':len(opts),'cases':rec,
   'seconds':time.monotonic()-st,
   'interpretation':'UNSAT/UNKNOWN are diagnostics, not kernel proofs. n is an integer in every case.'}
 (Path(__file__).resolve().parents[1]/'research/JSP404_UNIFORM_FOUR_ROW_DIAGNOSTIC_20261004.json').write_text(
   json.dumps(report,ensure_ascii=False,indent=2)+'\n')
