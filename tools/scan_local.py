"""Test the LOCAL-GADGET conjecture for the high selection theorem:

  consistent (LP-feasible) skeleton in a W>5/2 profile
    ==> exists a score-2 gadget that is either
        * a pure cap (direct angle with q_arc >= n), or
        * a single fan (+1 or -1) whose charge/cap eval gives
          bound >= 1.

For control, also report which local mechanism fires and at which
vertex, and record any feasible skeleton needing more.

Usage: python3 scan_local.py [max_feas_per_profile] [time_budget]
"""
import sys, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import generic_cegis as gce
import link_graph as lg
from scan_high import PROFILES, lp_feas

N = S = 4


def local_max(ctx):
    """Best bound among pure gadgets and single-fan gadgets.
    Returns (best_res, kind) where kind in {'pure','fan+','fan-'}."""
    best = lg.pure_gadget(ctx)
    kind = 'pure' if best is not None else None
    for v in range(ctx.s):
        for fw in (1, -1):
            r = lg.eval_chain(ctx, 0, [], {v: fw})
            if r is not None and (best is None
                                  or r['bound'] > best['bound']):
                best = r
                kind = 'fan+' if fw == 1 else 'fan-'
    return best, kind


def full_max(ctx):
    return lg.enumerate_max(ctx.sol, ctx.n, ctx.s)


def main():
    max_feas = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 600
    for d, ks in PROFILES:
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        feas = inf = 0
        tally = {}
        fails = []
        t0 = time.time()
        for sol, idxs, sig in ge.gen_cases(list(ks), N, S,
                                         VV=VV, sigvars=sigvars):
            sol = [dict(x) for x in sol]
            st, lo = lp_feas(sol)
            if st != 'bounded':
                inf += 1
                continue
            feas += 1
            ctx = lg.Ctx(sol, N, S)
            res, kind = local_max(ctx)
            bb = None if res is None else res['bound']
            if bb is None or bb < 1:
                # escalate to full enumeration for diagnostics
                res2 = full_max(ctx)
                b2 = None if res2 is None else res2['bound']
                fails.append((idxs, bb, kind, b2, res2))
                print(f'  LOCALFAIL d={d} idxs={idxs} local={bb} '
                      f'full={b2}', flush=True)
            else:
                key = (kind, str(bb))
                tally[key] = tally.get(key, 0) + 1
            if feas >= max_feas or time.time() - t0 > budget:
                break
        print(f'd={d} ks={ks} feas={feas} inf={inf} fails={len(fails)} '
              f'tally={tally} ({time.time()-t0:.0f}s)', flush=True)


if __name__ == '__main__':
    main()
