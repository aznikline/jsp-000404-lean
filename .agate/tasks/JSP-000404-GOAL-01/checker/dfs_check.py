"""Full DFS over carry subsets for the marginal deficit cases:
does ANY feasible carry pattern achieve wE >= F?"""
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve
from emission_analyze import adj_pairs, pair_data

cases = [
    [(0,0,1),(0,0,1),(0,0,3),(0,2,1)],
    [(0,0,1),(0,0,1),(2,0,1),(0,0,3)],
    [(0,0,1),(0,0,3),(0,2,1),(0,0,1)],
    [(0,0,1),(2,0,1),(0,0,3),(0,0,1)],
    [(0,0,3),(0,0,1),(0,0,1),(2,0,1)],
    [(0,0,3),(0,2,1),(0,0,1),(0,0,1)],
    [(0,2,1),(0,0,1),(0,0,1),(0,0,3)],
    [(2,0,1),(0,0,3),(0,0,1),(0,0,1)],
]
n, d, s = 3, Fr(1,4), 4
nv = s*(s-1)

for assign in cases:
    ks = [sum(max(m-1,0) for m in v) for v in assign]
    F = sum(2**k for k in ks)
    rows0 = base_rows(assign, n, s, d)
    pairs = pair_data(assign, s)
    autos = {}
    for v in range(s):
        for (a,b) in adj_pairs(s):
            if assign[v][a]>=1 and assign[v][b]>=1:
                autos.setdefault(v,set()).add((a,b))
    def wE(S):
        Sset=set(S); tot=0
        for v in range(s):
            E=0
            for (a,b) in adj_pairs(s):
                auto=1 if (a,b) in autos.get(v,()) else 0
                car=1 if (v,v*(s-1)+a,v*(s-1)+b,a,b) in Sset else 0
                E+=(2**(auto+car)-1)
            tot+=(2**ks[v])*E
        return tot
    def feas(S):
        rows=list(rows0)
        for (_,x,y,_,_) in S:
            rows.append(({x:Fr(-1),y:Fr(-1)},Fr(-1)))
        return lp_solve(rows,nv)
    best=[0,None]; nodes=[0]
    def dfs(i,S):
        nodes[0]+=1
        if nodes[0]>4000: return
        # upper bound prune: even adding ALL remaining can't beat best?
        if i==len(pairs):
            w=wE(S)
            if w>best[0]: best[0],best[1]=w,list(S)
            return
        # optimistic: all remaining pairs carry
        ub = wE(S + pairs[i:])
        if ub <= best[0] and best[0]>0:
            # still explore? if ub<=best and we only want existence of >=F,
            # prune when ub<F
            pass
        dfs(i+1,S)
        S.append(pairs[i])
        if feas(S):
            dfs(i+1,S)
        S.pop()
    dfs(0,[])
    print('assign=%s F=%d best_wE=%d %s carries=%s' %
          (assign, F, best[0], 'REACHABLE' if best[0]>=F else 'UNREACHABLE', best[1]))
