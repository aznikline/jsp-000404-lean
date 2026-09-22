"""Verify the saturated-vertex dichotomy:

saturated v (k = n-1, qs = (n,0,...,0) up to rotation) admits a
LOCAL delta>=1 gadget (pure cap via a direct arc containing the
heavy cell, or fan+charge via a complementary arc avoiding it) IFF
the bit pattern is not the split aligned with the heavy cell.

'good' := exists pair u,w with
    bits(u)==bits(w) and heavy in arc(u,w)   [pure cap]
 OR bits(u)!=bits(w) and heavy not in arc(u,w) [comp charge q=0]

'bad' := for every pair, bits differ iff arc contains heavy cell.
"""
import sys, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import link_graph as lg
import eval_ext as ex
from scan_high import lp_feas

N = S = 4
PROFILES = [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 0, 2), (0, 0, 0, 3),
            (0, 0, 1, 1), (0, 0, 1, 2), (0, 0, 1, 3)]


def heavy_pos(ctx, v):
    """position of the q=n cell, or None if not saturated."""
    qs = ctx.qs_b[v]
    hs = [g for g, q in enumerate(qs) if q == N]
    if len(hs) == 1 and all(q == 0 for g, q in enumerate(qs)
                            if g != hs[0]):
        return hs[0]
    return None


def sat_status(ctx, v):
    """'good'/'bad'/None(non-saturated) + witness description."""
    hp = heavy_pos(ctx, v)
    if hp is None:
        return None
    bits = ctx.bits_b[v]
    pos = ctx.pos_b[v]
    others = [t for t in range(S) if t != v]
    good = []
    for a, b in itertools.combinations(others, 2):
        lo, hi = sorted((pos[a], pos[b]))
        has_heavy = lo <= hp < hi
        if bits[a] == bits[b] and has_heavy:
            good.append(('pure', a, b))
        if bits[a] != bits[b] and not has_heavy:
            good.append(('charge', a, b))
    if good:
        return ('good', good)
    return ('bad',)


def main():
    tot = {'good': 0, 'bad': 0}
    bad_examples = []
    # sanity: 'good' must imply an actual gadget bound>=1 via the
    # predicted gadget (pure cap or fan+charge)
    mism = 0
    for d in PROFILES:
        ks = list(N - 1 - x for x in d)
        VV = ge.build_VV(ks, N, S)
        sigvars = ge.build_sigvars(VV, S)
        for sol, idxs, sig in ge.gen_cases(ks, N, S,
                                           VV=VV, sigvars=sigvars):
            sol = [dict(x) for x in sol]
            st, lo = lp_feas(sol)
            if st != 'bounded':
                continue
            ctx = lg.Ctx(sol, N, S)
            for v in range(S):
                stt = sat_status(ctx, v)
                if stt is None:
                    continue
                if stt[0] == 'good':
                    tot['good'] += 1
                    # verify: predicted gadget really gives bound 1
                    kind = stt[1][0][0]
                    if kind == 'pure':
                        r = lg.pure_gadget(ctx)
                        ok = r is not None and r['bound'] >= 1
                    else:
                        r = lg.eval_chain(ctx, 0, [], {v: 1})
                        ok = r is not None and r['bound'] >= 1
                    if not ok:
                        mism += 1
                        if mism < 5:
                            print('MISMATCH good-but-fail', d, idxs, v,
                                  stt[1][0])
                else:
                    tot['bad'] += 1
                    if len(bad_examples) < 3:
                        bad_examples.append((d, idxs, v))
        print('profile', d, 'done', tot, flush=True)
    print('total', tot, 'good-but-gadget-fails:', mism)
    print('bad examples:', bad_examples)


if __name__ == '__main__':
    main()
