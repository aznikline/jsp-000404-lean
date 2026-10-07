#!/usr/bin/env python3
"""Bounded pure DBM certificate generation for the fixed-n4 SixOuter CORE75.
No Lean run, no solver axiom, no global generation. One supplied acyclic mask
is only a pilot; final mathematical coverage must split all actual triangles.
"""
from pathlib import Path
from itertools import combinations
import argparse,json,hashlib,time,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from export_six_exact_floor_kernel_20261005 import row_orders,EDGES,TRIPLES

# Arc=(source,target,constant,delta_coefficient,strict,origin).
def geometry(mask):
    a=[]
    def put(u,v,c,b,s,origin):a.append((u,v,c,b,s,origin))
    for i in range(5):
        put(('t',i),('z',),0,0,False,('thetaLower',i))
        put(('z',),('t',i),0,1,False,('thetaUpper',i))
        if i<4:put(('t',i+1),('t',i),0,0,True,('thetaOrder',i))
    for e in EDGES:
        i,j=e;put(('d',i,j),('t',i),-1,0,False,('corridorLower',i,j))
        put(('t',j),('d',i,j),3,1,False,('corridorUpper',i,j))
    for bit,(i,j,k) in enumerate(TRIPLES):
        x,y,z=('d',i,j),('d',i,k),('d',j,k)
        lo,hi=(z,x) if mask>>bit&1 else (x,z)
        put(hi,lo,-1,0,False,('triangle',bit,0))
        put(y,lo,0,0,True,('triangle',bit,1))
        put(hi,y,0,0,True,('triangle',bit,2))
    return a

def endpoints(rows,i,k):
    xs=[('d',*e) for e in rows[i]]
    before=('t',i) if k==0 else xs[k-1]
    after=('t',i) if k==4 else xs[k]
    return before,after,4 if k==4 else 0,1 if k==4 else 0

def low_profiles():
    profiles=[]
    for k in range(5):profiles.append([3 if j==k else 0 for j in range(5)])
    for pair in combinations(range(5),2):profiles.append([2 if j in pair else 0 for j in range(5)])
    return profiles

def profile_arcs(rows,p,t):
    arcs=[]
    for i in [1,3]:
        lower=low_profiles()[p] if i==1 else [2 if k==t else 0 for k in range(5)]
        for k in range(5):
            before,after,c,b=endpoints(rows,i,k)
            arcs.append((after,before,c-lower[k],b,False,('gapLower',i,k)))
            if i==3:arcs.append((before,after,(3 if k==t else 2)-c,-b,True,('gapUpper',i,k)))
    return arcs

def negative_cycle(arcs):
    vertices=sorted({a[0] for a in arcs}|{a[1] for a in arcs})
    dist={v:(0,0,0) for v in vertices};parent={};last=None
    # Exact ordered-group weights at delta=1-epsilon with strict infinitesimal.
    for _ in vertices:
        last=None
        for ix,(u,v,c,b,s,_) in enumerate(arcs):
            step=(c+b,-b,-int(s));cand=tuple(a+b for a,b in zip(dist[u],step))
            if cand<dist[v]:dist[v]=cand;parent[v]=(u,ix);last=v
        if last is None:raise RuntimeError('no negative cycle near delta1')
    v=last
    for _ in vertices:v=parent[v][0]
    start=v;back=[]
    while True:
        u,ix=parent[v];back.append(ix);v=u
        if v==start:break
        assert len(back)<=len(vertices)
    path=[arcs[ix] for ix in reversed(back)]
    assert all(path[j][1]==path[(j+1)%len(path)][0] for j in range(len(path)))
    # Canonical rotation, preserving the real decoder origin of every edge.
    path=min(tuple(path[k:]+path[:k]) for k in range(len(path)))
    A=sum(a[2] for a in path);B=sum(a[3] for a in path);strict=any(a[4] for a in path)
    accepts=B>=0 and A+B<=0 and (A+B<0 or B>0 or strict)
    if not accepts:raise RuntimeError(('existing_universal_accepts_rejects',A,B,strict,path))
    return path

def emit_lean(result,target):
    def vertex(v):
        if v[0]=='z':return '.zero'
        if v[0]=='t':return f'.theta {v[1]}'
        return f'.distance {v[1]} {v[2]}'
    def vector(items):return '!['+', '.join(items)+']'
    def origin(o):return '.'+o[0]+' '+ ' '.join(map(str,o[1:]))
    text=['import Jsp000404.SixOuterReplay','',
      '/-! SOURCE_ONLY one-mask CORE75 pilot. No all-word coverage or Lean PASS is claimed. -/',
      'set_option autoImplicit false','set_option maxRecDepth 8192','set_option maxHeartbeats 0','',
      f'namespace Jsp404.SixOuterMask{result["mask"]:03d}Data','open SixOuterReplay','',
      'def word : Word := '+vector(['true' if result['mask']>>i&1 else 'false' for i in range(10)]),'',
      'def rows : RowsData := '+vector([vector([str(e[1] if e[0]==i else e[0]) for e in result['rows'][str(i)]]) for i in range(5)]),'']
    for ix,cycle in enumerate(result['cycles']):
        nodes=[e['source'] for e in cycle]+[cycle[-1]['target']]
        text += [f'def localCycle{ix:03d} : Cycle where',f'  length := {len(cycle)}','  data := {',
          '    node := '+vector([vertex(v) for v in nodes]),
          '    constant := '+vector([str(e['constant']) for e in cycle]),
          '    coefficient := '+vector([str(e['coefficient']) for e in cycle]),
          '    strict := '+vector(['true' if e['strict'] else 'false' for e in cycle])+' }',
          '  origin := '+vector([origin(e['origin']) for e in cycle]),'']
    text += ['def library : Library']
    text += [f'  | {i} => some localCycle{i:03d}' for i in range(result['unique_cycles'])]
    text += ['  | _ => none','']
    ids={(c['low_profile'],c['tail3_profile']):c['cycle'] for c in result['contexts']}
    text += ['def ids : Fin 15 → Fin 5 → ℕ := '+vector([vector([str(ids[p,t]) for t in range(5)]) for p in range(15)]),'',
      'theorem point_checked : leafCheck library word rows ids = true := by decide','',
      '#print axioms point_checked',f'end Jsp404.SixOuterMask{result["mask"]:03d}Data','']
    target.write_text('\n'.join(text))
    return {'path':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'bytes':target.stat().st_size,'status':'SOURCE_ONLY_NOT_LEAN_CHECKED'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--mask',type=int,default=0);ap.add_argument('--out',type=Path,default=Path('.lake/oct8-critical22-six/pilot-mask000.json'));ap.add_argument('--emit-source',type=Path);args=ap.parse_args()
    t=time.monotonic();rows=row_orders(args.mask);assert rows is not None
    cycles=[];lookup={};contexts=[]
    for p in range(15):
        for tail in range(5):
            arcs=geometry(args.mask)+profile_arcs(rows,p,tail)
            path=negative_cycle(arcs)
            key=tuple(path)
            if key not in lookup:lookup[key]=len(cycles);cycles.append(path)
            # Independently replay every selected edge under this exact context.
            assert all(edge in arcs for edge in path)
            contexts.append({'low_profile':p,'tail3_profile':tail,'cycle':lookup[key]})
    result={'status':'SOURCE_ONLY_PURE_CERTIFICATE_DATA_NOT_LEAN_CHECKED','kernel_all_words':False,'Lean_run':False,
      'n':4,'delta_domain':'0<=delta<1; acceptance needs only delta<1',
      'core':'row1 score>=2, row3 score1; rows0,2,4 arbitrary',
      'mask':args.mask,'rows':{str(i):[list(e) for e in rows[i]] for i in range(5)},
      'weak_low_profiles':low_profiles(),'tail3_profiles':5,'contexts':contexts,
      'cycles':[[{'source':list(u),'target':list(v),'constant':c,'coefficient':b,'strict':s,'origin':list(o)} for u,v,c,b,s,o in path] for path in cycles],
      'unique_cycles':len(cycles),'context_count':len(contexts),'max_cycle_length':max(map(len,cycles)),
      'pure_replay_all_contexts':True,'existing_shared_universal_accepts_all_cycles':True,
      'seconds':time.monotonic()-t,'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'global_coverage':'NOT_GENERATED; actual triangle split plus all62 leaf proofs remains required'}
    if args.emit_source:result['emitted_source']=emit_lean(result,args.emit_source)
    args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','mask','context_count','unique_cycles','max_cycle_length','seconds']}))

if __name__=='__main__':main()
