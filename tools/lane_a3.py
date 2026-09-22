"""Staged minimal-gadget search: for each skeleton, the simplest
gadget family reaching bound >= 1/2.

Stages:
  0 pure caps
  1 single fan (+/-1)
  2 fan subsets (size>=2, all signs)
  3 one link (a,b,h,sig) + fan subsets
  4 two-link path (a-b-c, pivot h) + fan subsets
  5 closed 3-cycle over outer + fan subsets
  6 full enumerate_max (fallback)
"""
import sys, json, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import link_graph as lg
from lane_a import profile_data

HALF = F(1, 2)


def fan_subsets(s, maxsz=None):
    """Yield dicts v->±1 ordered by size (incl. empty)."""
    vs = range(s)
    yield {}
    for sz in range(1, s + 1):
        if maxsz and sz > maxsz:
            break
        for sub in itertools.combinations(vs, sz):
            for signs in itertools.product((1, -1), repeat=sz):
                yield dict(zip(sub, signs))


def stage_eval(ctx, max_link=3):
    """Return (stage, bestresult) for first stage with bound>=1/2,
    else (stage_of_best, best)."""
    n, s = ctx.n, ctx.s
    best = lg.pure_gadget(ctx)
    if best is not None and best['bound'] >= HALF:
        return 0, best
    fas = list(fan_subsets(s))
    # stage 1+2: fans only
    for fa in fas:
        r = lg.eval_chain(ctx, 0, [], fa)
        if r is not None and (best is None or r['bound'] > best['bound']):
            best = r
        if r is not None and r['bound'] >= HALF:
            return (1 if len(fa) == 1 else 2), r
    # stage 3: single link
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for a, b in itertools.combinations(outer, 2):
            for sig in (1, -1):
                edges = [(a, b, sig)]
                for fa in fas:
                    r = lg.eval_chain(ctx, h, edges, fa)
                    if r is not None and (
                            best is None or r['bound'] > best['bound']):
                        best = r
                    if r is not None and r['bound'] >= HALF:
                        return 3, r
    # stage 4: two-link path
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for a, b, c_ in itertools.permutations(outer, 3):
            for s1, s2 in itertools.product((1, -1), repeat=2):
                edges = [(a, b, s1), (b, c_, s2)]
                for fa in fas:
                    r = lg.eval_chain(ctx, h, edges, fa)
                    if r is not None and (
                            best is None or r['bound'] > best['bound']):
                        best = r
                    if r is not None and r['bound'] >= HALF:
                        return 4, r
    # stage 5: closed 3-cycle over the 3 outer vertices
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        if len(outer) == 3:
            a, b, c_ = outer
            for sg in itertools.product((1, -1), repeat=3):
                edges = [(a, b, sg[0]), (b, c_, sg[1]), (c_, a, sg[2])]
                for fa in fas:
                    r = lg.eval_chain(ctx, h, edges, fa)
                    if r is not None and (
                            best is None or r['bound'] > best['bound']):
                        best = r
                    if r is not None and r['bound'] >= HALF:
                        return 5, r
    return 6, best


def main():
    n = s = 4
    ks = json.loads(sys.argv[1])
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
    VV = ge.build_VV(ks, n, s)
    sigvars = ge.build_sigvars(VV, s)
    cnt = 0
    t0 = time.time()
    stages = {}
    hard = []
    for sol, idxs, sigk in ge.gen_cases(ks, n, s, VV=VV, sigvars=sigvars):
        cnt += 1
        if cnt > limit:
            break
        sol = [dict(x) for x in sol]
        ctx = lg.Ctx(sol, n, s)
        st, best = stage_eval(ctx)
        stages[st] = stages.get(st, 0) + 1
        if best is None or best['bound'] < HALF:
            hard.append((idxs, sigk, sol,
                         None if best is None else str(best['bound'])))
        elif st >= 5:
            hard.append((idxs, sigk, sol, 'stage5:' + str(best['bound'])))
    print(f'leaves={cnt} stages={stages} hard={len(hard)} '
          f'({time.time()-t0:.0f}s)', flush=True)
    for idxs, sigk, sol, b in hard[:20]:
        pd = profile_data(sol, n, s)
        print(f'idxs={idxs} best={b}')
        for v, p in enumerate(pd):
            print('   ', v, p)


if __name__ == '__main__':
    main()
