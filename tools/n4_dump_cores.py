"""Dump per-leaf tracked cores for all n=4 certificates.

Tracks only triples and E-facts (U-facts / corridor / base are free
`have` instantiations in Lean).  Output: tools/n4_cores.json
"""
import z3, itertools, json, sys, time
sys.path.insert(0, '/Users/wizout/op/learn/sunyuchen/jsp-wt-air-owner/tools')
from n4_model import *

OUT = 'n4_cores.json'

def track_sig(s, row, t_i, S, pv, kind, c):
    U, E = sig2_case(t_i, S, pv, c) if kind == 's2' \
        else sig1_case(t_i, S, pv, c)
    for tag, e in U: s.add(e)
    for tag, e in E: s.assert_and_track(e, f'E{row}_{tag}')

def leaf_core(spec, combos, em=None):
    """spec: [(row, kind)]; combos: [(case per row)]. Returns cores dict."""
    results = {}
    t0 = time.time()
    for combo in combos:
        delta, t, d, D, p, base, trips = build()
        s = z3.Solver(); s.set("timeout", 60000)
        s.add(base)
        for ij, tr in trips.items():
            s.assert_and_track(tr, 'tr%d%d%d' % ij)
        for (row, kind), c in zip(spec, combo):
            S = [D(row, j) for j in range(P) if j != row]
            track_sig(s, row, t[row], S, p, kind, c)
        key = ','.join(str(c) for c in combo)
        if em is not None:
            ems = [em_case(t, D, p, r, w)
                   for r, w in [(0,1),(0,2),(0,3),(4,1),(4,2),(4,3)]]
            s.assert_and_track(z3.Or(*ems), 'em')
        if s.check() != z3.unsat:
            results[key] = 'SAT'
            continue
        results[key] = sorted(str(u) for u in s.unsat_core())
    return results

def main():
    allres = {}
    # pair_A: AA(2,3) / AA(3,4): row1 s2, row3 s1
    print('pair_A (1:s2, 3:s1)...', flush=True)
    allres['pair_A'] = leaf_core([(1,'s2'),(3,'s1')],
                                 [(a,b) for a in range(15) for b in range(5)])
    # pair_B: AB(0,1) / AB(1,2): row1 s1, row3 s2
    print('pair_B (1:s1, 3:s2)...', flush=True)
    allres['pair_B'] = leaf_core([(1,'s1'),(3,'s2')],
                                 [(a,b) for a in range(5) for b in range(15)])
    # triple_A: AA(2,4): rows 1:s2, 2:s1, 4:s1
    print('triple_A (1:s2, 2:s1, 4:s1)...', flush=True)
    allres['triple_A'] = leaf_core([(1,'s2'),(2,'s1'),(4,'s1')],
        [(a,b,c) for a in range(15) for b in range(5) for c in range(5)])
    # triple_B: AB(0,2): rows 0:s1, 2:s1, 3:s2
    print('triple_B (0:s1, 2:s1, 3:s2)...', flush=True)
    allres['triple_B'] = leaf_core([(0,'s1'),(2,'s1'),(3,'s2')],
        [(a,b,c) for a in range(5) for b in range(5) for c in range(15)])
    # pair04_em: BT all: rows 0:s2, 4:s2 + emission Or
    print('pair04_em (0:s2, 4:s2, em)...', flush=True)
    allres['pair04_em'] = leaf_core([(0,'s2'),(4,'s2')],
        [(a,b) for a in range(15) for b in range(15)], em=True)
    with open(OUT, 'w') as f:
        json.dump(allres, f, indent=0)
    nsat = {k: [kk for kk,v in allres[k].items() if v=='SAT']
            for k in allres}
    print('sat leaves:', nsat)
    print('total time', time.time()-t0)

if __name__ == '__main__':
    main()
