#!/usr/bin/env python3
"""One-word SOURCE_ONLY A75/B225 pilots; no Lean or all62 generation."""
from pathlib import Path
import argparse,json,hashlib,time
from export_six_outer_pilot_20261008 import geometry,endpoints,low_profiles,negative_cycle,row_orders

def lower(family,p,q,i,k):
    if family=='A':
        return low_profiles()[p][k] if i==1 else (2 if i==3 and k==q else 0)
    return low_profiles()[p][k] if i==0 else (low_profiles()[q][k] if i==2 else 0)

def arcs(rows,family,p,q):
    out=[]
    for i in range(5):
        for k in range(5):
            before,after,c,b=endpoints(rows,i,k)
            out.append((after,before,c-lower(family,p,q,i,k),b,False,('gapLower',i,k)))
    return out

def emit(result,target):
    vertex=lambda v: '.zero' if v[0]=='z' else (f'.theta {v[1]}' if v[0]=='t' else f'.distance {v[1]} {v[2]}')
    vector=lambda xs:'!['+', '.join(xs)+']'
    origin=lambda o:'.'+o[0]+' '+' '.join(map(str,o[1:]))
    prefix='SixWeakOuter' if result['family']=='A' else 'SixDoubleLow'
    namespace=f'{prefix}Mask{result["mask"]:03d}Data';N=5 if result['family']=='A' else 15
    text=['import Jsp000404.SixWeakOuterReplay','','/-! SOURCE_ONLY one-real-word finite pilot. No kernel or all-word claim. -/',
      'set_option autoImplicit false','set_option maxRecDepth 8192','set_option maxHeartbeats 0','',
      f'namespace Jsp404.{namespace}','open SixOuterReplay SixWeakOuterReplay','',
      'def word : Word := '+vector(['true' if result['mask']>>i&1 else 'false' for i in range(10)]),'',
      'def rows : RowsData := '+vector([vector([str(e[1] if e[0]==i else e[0]) for e in result['rows'][str(i)]]) for i in range(5)]),'']
    for ix,cycle in enumerate(result['cycles']):
        nodes=[e['source'] for e in cycle]+[cycle[-1]['target']]
        text += [f'def localCycle{ix:03d} : Cycle where',f'  length := {len(cycle)}','  data := {',
          '    node := '+vector([vertex(v) for v in nodes]),'    constant := '+vector([str(e['constant']) for e in cycle]),
          '    coefficient := '+vector([str(e['coefficient']) for e in cycle]),
          '    strict := '+vector(['true' if e['strict'] else 'false' for e in cycle])+' }',
          '  origin := '+vector([origin(e['origin']) for e in cycle]),'']
    text += ['def library : Library']+[f'  | {i} => some localCycle{i:03d}' for i in range(len(result['cycles']))]+['  | _ => none','']
    ids={(c['first_profile'],c['second_profile']):c['cycle'] for c in result['contexts']}
    text += [f'def ids : Fin 15 → Fin {N} → ℕ := '+vector([vector([str(ids[p,q]) for q in range(N)]) for p in range(15)]),'',
      f'theorem point_checked : leafCheck{result["family"]} library word rows ids = true := by decide','',
      '#print axioms point_checked',f'end Jsp404.{namespace}','']
    target.write_text('\n'.join(text));return {'path':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'bytes':target.stat().st_size}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--family',choices=['A','B'],required=True);ap.add_argument('--mask',type=int,default=472);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--emit-source',type=Path);args=ap.parse_args()
    started=time.monotonic();rows=row_orders(args.mask);assert rows is not None
    contexts=[];cycles=[];seen={};N=5 if args.family=='A' else 15
    for p in range(15):
        for q in range(N):
            available=geometry(args.mask)+arcs(rows,args.family,p,q);path=negative_cycle(available)
            assert all(e in available for e in path)
            if path not in seen:seen[path]=len(cycles);cycles.append(path)
            contexts.append({'first_profile':p,'second_profile':q,'cycle':seen[path]})
    result={'status':'SOURCE_ONLY_NOT_LEAN_CHECKED','family':args.family,'mask':args.mask,'n':4,'delta_domain':'0<=delta<1',
      'rows':{str(i):[list(e) for e in rows[i]] for i in range(5)},'contexts':contexts,
      'cycles':[[{'source':list(u),'target':list(v),'constant':c,'coefficient':b,'strict':s,'origin':list(o)} for u,v,c,b,s,o in cycle] for cycle in cycles],
      'context_count':len(contexts),'unique_cycles':len(cycles),'max_cycle_length':max(map(len,cycles)),
      'all_edges_independently_replayed':True,'all_cycles_old_universal_accepts':True,'upper_gap_arcs_used':False,
      'all62_generated':False,'Lean_run':False,'seconds':time.monotonic()-started,'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if args.emit_source:result['emitted_source']=emit(result,args.emit_source)
    args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','family','mask','context_count','unique_cycles','max_cycle_length','seconds']}))

if __name__=='__main__':main()
