"""Deterministic all-bad gadget selector: a finite case tree whose
every branch is an explicit gadget template.  Measures per-branch
coverage over allbad_dump records and prints uncovered records.

Branches (in order):
  PURE  : some vertex (usually non-sat) has direct arc q >= n.
  BLOCK : block_gadgets (charge-in-cap, no equalities).
  FAN0  : fan{v:+1} alone reaches bound 1 (non-sat v, B_v=0 charge).
  STRIP : canonical strips - fan at a bad or non-sat vertex plus the
          two negative links on triangles {i,j,x} / {i,j,y} or
          {f,i,x}/{f,x,y}, evaluated by eval_chain2.
  EM2   : fallback (full grammar) - counted separately.
"""
import sys, json, itertools, collections, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import link_graph as lg
import eval_ext as ex
from allbad_dump import heavy_pos, is_bad, PROFILES, N, S


def rebuild(rec, look):
    sol = []
    for v, vd in enumerate(rec['vdata']):
        key = (tuple(vd['order']),
               tuple(sorted((int(k), b) for k, b in vd['bits'].items())),
               tuple(vd['qs']))
        sol.append(look[v][key])
    return sol


def select(ctx, sat):
    """Deterministic selector; returns (branch, res|desc)."""
    r = lg.pure_gadget(ctx)
    if r is not None and r['bound'] >= 1:
        return 'PURE', r
    bg = ex.block_gadgets(ctx)
    if bg is not None and bg[0] >= F(1):
        return 'BLOCK', bg
    nonsat = [v for v in range(S) if v not in sat]
    # fan-alone at non-saturated vertices
    for v in nonsat:
        res = ex.eval_chain2(ctx, 0, [], {v: 1})
        if res is not None and res['bound'] >= 1:
            return 'FAN0', res
    i, j = sorted(sat)[:2]
    # all 2-link sets over a shared pivot: h pivot, edges = pairs of
    # the other 3 vertices (3 possible edges => 3 edge-pairs), all
    # sign combos
    def strips(fans):
        for h in range(S):
            outer = [v for v in range(S) if v != h]
            es = list(itertools.combinations(outer, 2))
            for (a, b), (c, d2) in itertools.combinations(es, 2):
                for s1 in (1, -1):
                    for s2 in (1, -1):
                        yield h, [(a, b, s1), (c, d2, s2)]
            for (a, b) in es:
                for s1 in (1, -1):
                    yield h, [(a, b, s1)]

    # STRIP-A: fan at a non-sat vertex + <=2 signed links
    for f in nonsat:
        for h, edges in strips({f: 1}):
            res = ex.eval_chain2(ctx, h, edges, {f: 1})
            if res is not None and res['bound'] >= 1:
                return 'STRIP-A', res
    # STRIP-B: fan at a bad vertex + <=2 signed links
    for f in (i, j):
        for h, edges in strips({f: 1}):
            res = ex.eval_chain2(ctx, h, edges, {f: 1})
            if res is not None and res['bound'] >= 1:
                return 'STRIP-B', res
    # STRIP-C: <=2 links, no fan
    for h, edges in strips({}):
        res = ex.eval_chain2(ctx, h, edges, {})
        if res is not None and res['bound'] >= 1:
            return 'STRIP-C', res
    # STRIP-D: two fans (any vertices) + <=2 links
    for f1 in range(S):
        for f2 in range(f1 + 1, S):
            for w1 in (1, -1):
                for w2 in (1, -1):
                    fa = {f1: w1, f2: w2}
                    for h, edges in strips(fa):
                        res = ex.eval_chain2(ctx, h, edges, fa)
                        if res is not None and res['bound'] >= 1:
                            return 'STRIP-D', res
    # STRIP-E: three fans + <=2 links
    for f1, f2, f3 in itertools.combinations(range(S), 3):
        for ws in itertools.product((1, -1), repeat=3):
            fa = {f1: ws[0], f2: ws[1], f3: ws[2]}
            for h, edges in strips(fa):
                res = ex.eval_chain2(ctx, h, edges, fa)
                if res is not None and res['bound'] >= 1:
                    return 'STRIP-E', res
    return 'NONE', None


def main():
    fn = sys.argv[1] if len(sys.argv) > 1 else 'allbad_dump.json'
    recs = json.load(open(fn))
    ks = tuple(recs[0]['profile']) if recs else (3, 3, 2, 2)
    ks = PROFILES[ks]
    VV = ge.build_VV(list(ks), N, S)
    look = [{(vv['order'], tuple(sorted(vv['bits'].items())), vv['qs']): vv
            for vv in VV[v]} for v in range(S)]
    recs = json.load(open(fn))
    tally = collections.Counter()
    bypat = collections.defaultdict(collections.Counter)
    uncovered = []
    t0 = time.time()
    for n, r in enumerate(recs):
        sol = rebuild(r, look)
        ctx = lg.Ctx(sol, N, S)
        sat = set(r['sat'])
        br, res = select(ctx, sat)
        tally[br] += 1
        p = r['pairs'][0]
        bypat[(p['slot_i'], p['slot_j'])][br] += 1
        if br == 'NONE':
            uncovered.append(n)
            if len(uncovered) <= 20:
                print('NONE', n, r['idxs'], p['slot_i'], p['slot_j'],
                      r['lo'], flush=True)
        if n % 2000 == 0:
            print(f'  ... {n} ({time.time()-t0:.0f}s) '
                  f'{dict(tally)}', flush=True)
    print('tally:', dict(tally))
    print('by slot:', {k: dict(v) for k, v in bypat.items()})
    print('uncovered:', len(uncovered), uncovered[:50])


if __name__ == '__main__':
    main()
