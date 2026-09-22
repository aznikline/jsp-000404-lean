"""Full coverage test: enriched gadget grammar vs LP level 2.

For every mode-A-consistent skeleton of every W>5/2 profile at
s=n=4, test whether the gadget grammar finds bound >= 1:

  * block gadgets (inequality-only charge-cap, eval_ext.block_gadgets)
  * enumerate_max edge/fan grammar (one pivot; open paths and closed
    cycles over subsets of the other vertices; all fan sign
    assignments) evaluated by eval_ext.eval_chain2 (nn caps +
    charge-reduced caps + multiset covers).

Usage: python3 cover3.py d0 d1 d2 d3
"""
import sys, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import link_graph as lg
import eval_ext as ex
from scan_high import lp_feas
from scan_vertices import vertex_mode

N = S = 4


def em2(ctx):
    """enumerate_max grammar evaluated by eval_chain2."""
    best = None
    fas = list(lg.fan_assignments(S))
    for h in range(S):
        outer = [v for v in range(S) if v != h]
        for r_ in range(0, len(outer) + 1):
            perms = [()] if r_ == 0 else itertools.permutations(outer, r_)
            for perm in perms:
                for closed in (False, True):
                    for edges in lg.edge_lists(list(perm), closed):
                        for fa in fas:
                            res = ex.eval_chain2(ctx, h, edges, fa)
                            if res is not None and (
                                    best is None or
                                    res['bound'] > best['bound']):
                                best = res
                            if best is not None and best['bound'] >= 1:
                                return best
    return best


def main():
    d = tuple(int(x) for x in sys.argv[1:5])
    ks = tuple(N - 1 - x for x in d)
    W = sum(F(2) ** (-x) for x in d)
    VV = ge.build_VV(list(ks), N, S)
    sigvars = ge.build_sigvars(VV, S)
    feas = 0
    nocov = []
    tally = {}
    t0 = time.time()
    for sol, idxs, sig in ge.gen_cases(list(ks), N, S,
                                     VV=VV, sigvars=sigvars):
        sol = [dict(x) for x in sol]
        st, lo = lp_feas(sol)
        if st != 'bounded':
            continue
        feas += 1
        ctx = lg.Ctx(sol, N, S)
        bg = ex.block_gadgets(ctx)
        if bg is not None and bg[0] >= F(1):
            tally['block'] = tally.get('block', 0) + 1
            continue
        r = lg.pure_gadget(ctx)
        if r is not None and r['bound'] >= 1:
            tally['pure'] = tally.get('pure', 0) + 1
            continue
        best = em2(ctx)
        if best is not None and best['bound'] >= 1:
            tag = (len(best['edges']), len(best['fans']))
            tally[str(tag)] = tally.get(str(tag), 0) + 1
        else:
            nocov.append((idxs, None if best is None else best['bound']))
            print('  NOCOV', idxs,
                  None if best is None else best['bound'], flush=True)
        if time.time() - t0 > 2400:
            print('  TIMEOUT at feas=', feas, flush=True)
            break
    print(f'd={d} ks={ks} W={float(W)} feas={feas} nocov={len(nocov)}',
          flush=True)
    print('  tally:', tally, flush=True)


if __name__ == '__main__':
    main()
