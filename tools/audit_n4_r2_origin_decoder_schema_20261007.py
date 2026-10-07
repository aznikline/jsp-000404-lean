#!/usr/bin/env python3
"""Finite source-profile/origin parity audit; deliberately not a Lean proof."""
from __future__ import annotations
import argparse, gzip, hashlib, itertools, json, re, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
TRIPLES=list(itertools.combinations(range(7),3))

def origin(name):
    if m:=re.fullmatch(r'ht([0-6])([ab])',name):
        return ('thetaLower' if m[2]=='a' else 'thetaUpper',int(m[1]))
    if m:=re.fullmatch(r'ht([0-6])([0-6])',name):
        i,j=map(int,m.groups());assert j==i+1
        return ('thetaNext',i)
    if m:=re.fullmatch(r'hc([0-6])([0-6])([ab])',name):
        return ('corridorLower' if m[3]=='a' else 'corridorUpper',int(m[1]),int(m[2]))
    if m:=re.fullmatch(r'htr([0-6])([0-6])([0-6])([abc])',name):
        tri=tuple(map(int,m.groups()[:3]));return ('triangle',TRIPLES.index(tri),'abc'.index(m[4]))
    if m:=re.fullmatch(r'hgap([0-6])([0-6])(lower|upper)',name):
        return ('gapLower' if m[3]=='lower' else 'gapUpper',int(m[1]),int(m[2]))
    raise ValueError(name)

def d(i,j):return 'd'+str(min(i,j))+str(max(i,j))
def row_orders(word):
    ranks={i:{j:0 for j in range(7) if j!=i} for i in range(7)}
    for bit,(i,j,k) in zip(word,TRIPLES):
        for row,left,right in ((i,j,k),(j,i,k),(k,i,j)):
            ranks[row][left if bit else right]+=1
    assert all(sorted(v.values())==list(range(6)) for v in ranks.values())
    return {i:sorted(v,key=v.get) for i,v in ranks.items()}

def decode(word,orders,profiles,tag,table):
    kind,*args=tag
    if kind=='thetaLower':return ('t'+str(args[0]),'zero',0,0,False)
    if kind=='thetaUpper':return ('zero','t'+str(args[0]),0,1,False)
    if kind=='thetaNext':return ('t'+str(args[0]+1),'t'+str(args[0]),0,0,True)
    if kind.startswith('corridor'):
        i,j=args
        if not i<j:return None
        return (d(i,j),'t'+str(i),-1,0,False) if kind=='corridorLower' else ('t'+str(j),d(i,j),3,1,False)
    if kind=='triangle':
        t,part=args;i,j,k=TRIPLES[t];lo,hi=(d(j,k),d(i,j)) if word[t] else (d(i,j),d(j,k))
        return ((hi,lo,-1,0,False),(d(i,k),lo,0,0,True),(hi,d(i,k),0,0,True))[part]
    i,k=args
    before='t'+str(i) if k==0 else d(i,orders[i][k-1])
    after='t'+str(i) if k==6 else d(i,orders[i][k])
    c,b=(4,1) if k==6 else (0,0)
    if kind=='gapUpper':
        if not 0<i<6:return None
        return (before,after,2-c,-b,True)
    if i in (0,6):
        if i not in profiles:return None
        lower=table[profiles[i]][k]
        if lower==0:return None
    else:lower=0
    return (after,before,c-lower,b,False)

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--prefer-compressed',action='store_true');args=parser.parse_args()
    start=time.monotonic();report=ROOT/'research/JSP404_N4_R2_PACKET_TAIL_COMPLETE_PAIRS_20261006.json'
    src=ROOT/'Jsp000404/N4R2ReifiedArcDecoder.lean'
    compressed=report.with_suffix('.json.gz')
    use_compressed=args.prefer_compressed or not report.exists()
    raw=gzip.decompress(compressed.read_bytes()) if use_compressed else report.read_bytes()
    data=json.loads(raw)
    text=src.read_text();block=text.split('def profileLower :',1)[1].split('def profilePairs',1)[0]
    table=[list(map(int,re.findall(r'\d+',row))) for row in re.findall(r'!\[([^]\n]+)\]',block)]
    assert len(table)==28 and all(len(row)==7 for row in table)
    expected=[[s+min(s,1) for s in entry['scores']] for entry in data['composition_catalog']]
    assert table==expected
    counts={};occurrences=0;cycle_ids=set();contexts=0;tag_cache={}
    def check(case,word,orders,profiles):
        nonlocal occurrences,contexts
        contexts+=1
        for cid in case['cycle_ids']:
            cycle_ids.add(cid)
            for arc in data['negative_cycle_registry'][cid]['actual_arcs']:
                name=arc[5];tag=tag_cache.setdefault(name,origin(name))
                actual=decode(word,orders,profiles,tag,table)
                assert actual is not None and tuple(arc[:5])==actual,(name,tag,actual,arc)
                counts[tag[0]]=counts.get(tag[0],0)+1;occurrences+=1
    for wr in data['word_records']:
        assert time.monotonic()-start<25,'bounded schema audit wall budget'
        word=list(map(int,wr['word']));orders=row_orders(word)
        if wr['stage']=='TAIL_GEOMETRY':check(wr,word,orders,{})
        elif wr['stage'].endswith('_WEAK28'):
            low=int(wr['stage'][3])
            for case in wr['profiles']:check(case,word,orders,{low:case['profile_id']})
        else:
            for low in (0,6):
                for case in wr['low_profiles'][str(low)]:check(case,word,orders,{low:case['profile_id']})
            for case in wr['pair_results']:check(case,word,orders,{0:case['profile0_id'],6:case['profile6_id']})
    # Reject unselected/zero low lowers and every low upper, including wrap.
    w=[0]*35;o=row_orders(w)
    rejected=0
    for i in (0,6):
        for k in range(7):
            for ps in ({},{i:0}):
                assert decode(w,o,ps,('gapUpper',i,k),table) is None;rejected+=1
            assert decode(w,o,{},('gapLower',i,k),table) is None;rejected+=1
            if k!=0:assert decode(w,o,{i:0},('gapLower',i,k),table) is None;rejected+=1
    result={'status':'SOURCE_PROFILE_AND_TYPED_ORIGIN_DATA_PARITY_PASS_NOT_KERNEL','audit_executes_Lean':False,'typed_module_compilation_evidence':'research/JSP404_N4_R2_REIFIED_ARC_DECODER_RECEIPT_20261007.json','original_eight_point_claimed':False,'complete_words':len(data['word_records']),'context_records_checked':contexts,'referenced_unique_cycles':len(cycle_ids),'actual_arc_occurrences_checked':occurrences,'origin_counts':counts,'unique_origin_names':len(tag_cache),'invalid_low_origins_rejected':rejected,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'report_sha256':hashlib.sha256(raw).hexdigest(),'report_bytes':len(raw),'input_encoding':'gzip' if use_compressed else 'json','compressed_input':'research/'+compressed.name,'compressed_sha256':hashlib.sha256(compressed.read_bytes()).hexdigest() if compressed.exists() else None,'elapsed_seconds':time.monotonic()-start}
    out=ROOT/'research/JSP404_N4_R2_ORIGIN_DECODER_SCHEMA_AUDIT_20261007.json';out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
