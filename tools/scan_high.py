"""Scan W>5/2 profiles (s=4,n=4): for each consistent skeleton, find
the cheapest gadget family reaching bound >= 1.

Families tried in order:
  pure    : pure_gadget (degenerate caps only)
  fan1    : single fan +-1, no links
  fan1L1  : single fan + one link (any pivot/sign)
  fan2L*  : small chains (|fans|<=2, |links|<=2)
  full    : enumerate_max fallback

Usage: python3 scan_high.py [per_profile_cap] [include_inf]
"""
import sys, json, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import generic_cegis as gce
import link_graph as lg

N = S = 4

PROFILES = [
    ((0, 0, 0, 0), (3, 3, 3, 3)),
    ((0, 0, 0, 1), (3, 3, 3, 2)),
    ((0, 0, 0, 2), (3, 3, 3, 1)),
    ((0, 0, 0, 3), (3, 3, 3, 0)),
    ((0, 0, 1, 1), (3, 3, 2, 2)),
    ((0, 0, 1, 2), (3, 3, 2, 1)),
    ((0, 0, 1, 3), (3, 3, 2, 0)),
]


def lp_feas(sol):
    gm.ORIG.clear()
    b = gm.build_case(sol, N, 'A')
    if b is None:
        return ('none', None)
    ineqs, eqs = b
    ineqs = gm.substitute(eqs, ineqs)
    return gce.lp_min_delta_f(ineqs)


def staged_max(ctx):
    """Cheapest sufficient gadget; returns (family, res)."""
    r = lg.pure_gadget(ctx)
    if r is not None and r['bound'] >= 1:
        return 'pure', r
    best = r
    s = ctx.s
    # stage: number of fans, links
    def try_eval(h, edges, fans):
        nonlocal best
        res = lg.eval_chain(ctx, h, edges, fans)
        if res is not None and (best is None
                                or res['bound'] > best['bound']):
            best = res
        return res

    one_fan = [{v: fw} for v in range(s) for fw in (1, -1)]
    two_fan = []
    for v1 in range(s):
        for v2 in range(v1 + 1, s):
            for f1 in (1, -1):
                for f2 in (1, -1):
                    two_fan.append({v1: f1, v2: f2})
    for fa in one_fan:
        r = lg.eval_chain(ctx, 0, [], fa)
        if r is not None and r['bound'] >= 1:
            return 'fan1', r
        if r is not None and (best is None
                              or r['bound'] > best['bound']):
            best = r
    # one link, all pivots/signs, with <=1 fan
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for a, b in itertools.combinations(outer, 2):
            for sig in (1, -1):
                for fa in [{}] + one_fan:
                    r = try_eval(h, [(a, b, sig)], fa)
                    if r is not None and r['bound'] >= 1:
                        return 'fan01L1', r
    # two fans + <=1 link; one fan + 2 links
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        links1 = [[(a, b, sig)]
                  for a, b in itertools.combinations(outer, 2)
                  for sig in (1, -1)]
        for fa in two_fan:
            for ed in [[]] + links1:
                r = try_eval(h, ed, fa)
                if r is not None and r['bound'] >= 1:
                    return 'fan2L01', r
        links2 = [e1 + e2 for i, e1 in enumerate(links1)
                  for e2 in links1[i:]]
        for fa in one_fan:
            for ed in links2:
                r = try_eval(h, ed, fa)
                if r is not None and r['bound'] >= 1:
                    return 'fan1L2', r
    # fallback: full enumeration
    res = lg.enumerate_max(ctx.sol, ctx.n, ctx.s)
    if res is not None and (best is None or res['bound'] > best['bound']):
        best = res
    return 'full', best


def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    include_inf = len(sys.argv) > 2
    for d, ks in PROFILES:
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        tally = {}
        seen = 0
        t0 = time.time()
        stop = False
        for sol, idxs, sig in ge.gen_cases(list(ks), N, S,
                                         VV=VV, sigvars=sigvars):
            sol = [dict(x) for x in sol]
            st, lo = lp_feas(sol)
            feas = (st == 'bounded')
            if not feas and not include_inf:
                continue
            seen += 1
            ctx = lg.Ctx(sol, N, S)
            fam, res = staged_max(ctx)
            bb = None if res is None else res['bound']
            key = (fam, 'INF' if not feas else 'F',
                   bb is not None and bb >= 1)
            tally[key] = tally.get(key, 0) + 1
            if bb is None or bb < 1:
                print(f'  LOW d={d} idxs={idxs} feas={feas} '
                      f'lo={lo} best={bb} fam={fam} res={res}',
                      flush=True)
            if seen >= cap:
                stop = True
                break
            if time.time() - t0 > 300:
                break
        print(f'd={d} ks={ks} seen={seen} tally={tally} '
              f'({time.time()-t0:.0f}s)', flush=True)


if __name__ == '__main__':
    main()
