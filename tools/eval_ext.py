"""Extended eval_chain: adds nn (comp angle >= 0) caps and full joint
cover search (any multiset of entries covering the negative block),
plus charge-cap blocks (comp charge arc A inside cap arc B).

Also adds 'block gadgets': no equalities at all - just per-vertex
inequality combinations.  We model these by allowing a *virtual*
positive block: choose a comp arc A (charge) and a cap B (any kind)
with A subseteq rng(B): bound contribution (1-q_A - B_B)/u_B.
Generalized: multiple disjoint charges inside one cap stack.
"""
import sys, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
import link_graph as lg

ZERO = F(0)


def eval_chain2(ctx, h, edges, fans):
    """Like eval_chain but cap options include nn caps and the cover
    is searched over multisets via per-gap LP-ish enumeration."""
    n, s = ctx.n, ctx.s
    R, con, dc = {}, ZERO, 0
    for v, fw in fans.items():
        Rd, cc, dd = ctx.fan[(v, fw)]
        for k, t in Rd.items():
            R[k] = R.get(k, 0) + t
        con += cc
        dc += dd
    for a, b, sig in edges:
        Rd, cc, dd = ctx.link[(min(a, b), max(a, b), h, sig)]
        for k, t in Rd.items():
            R[k] = R.get(k, 0) + t
        con += cc
        dc += dd
    c = -dc
    C = -con
    K = ZERO
    cap_vars = []
    for v in range(s):
        blk = {g: R.get((v, g), 0) for g in range(s - 1)}
        blk = {g: k for g, k in blk.items() if k != 0}
        if not blk:
            continue
        posblk = {g: k for g, k in blk.items() if k > 0}
        negblk = {g: -k for g, k in blk.items() if k < 0}
        if posblk:
            pset = frozenset(posblk)
            cand = []
            for rng, q in ctx.comp_ang[v]:
                if rng <= pset:
                    gain = min(posblk[g] for g in rng) * (F(1) - q)
                    if gain > 0:
                        cand.append((gain, rng))
            cand.sort(key=lambda t: -t[0])
            used = frozenset()
            for gain, rng in cand:
                if not (rng & used):
                    K += gain
                    used |= rng
        if negblk:
            # cap entries available at v: (range, B, u)
            ents = []
            for g in negblk:
                ents.append((frozenset([g]), F(1), ZERO))
            for rng, q in ctx.dir_ang[v]:
                ents.append((rng, F(n - 1) - q, F(1)))
            for rng, q in ctx.comp_ang[v]:
                ents.append((rng, F(n) - q, F(1)))
            # charge-reduced caps: a cap arc rng containing disjoint
            # comp charge arcs A_i has effective bound
            #   sum_{rng} r <= B - sum_i (1-q_{A_i}) + u*delta
            # on the leftover rng \\ union A_i.
            base = list(ents)
            chs = [(frozenset(rr), F(1) - qq)
                   for rr, qq in ctx.comp_ang[v] if F(1) - qq > 0]
            for rng, B, u in base:
                for k in range(1, len(chs) + 1):
                    for sel in itertools.combinations(chs, k):
                        if all(a <= rng for a, _ in sel):
                            uu = frozenset().union(*[a for a, _ in sel])
                            if len(uu) == sum(len(a) for a, _ in sel):
                                ents.append((rng - uu,
                                             B - sum(g for _, g in sel),
                                             u))
            # collect ALL covers as multisets of entries, then keep
            # the Pareto frontier of (Bcap, u).  A cap entry
            # (rng,B,u) taken with multiplicity m supplies m units
            # to EVERY gap in rng at once (joint cover), so applying
            # it decrements all uncovered gaps inside rng.
            covs = []

            def rec(rem, chosen):
                if not rem:
                    B = sum(e[1] * m for e, m in chosen)
                    u = sum(e[2] * m for e, m in chosen)
                    covs.append((B, u))
                    return
                g = min(rem)
                kappa = rem[g]
                for e in ents:
                    if g not in e[0]:
                        continue
                    for m in range(1, kappa + 1):
                        rem2 = {}
                        for h, k_ in rem.items():
                            left = k_ - (m if h in e[0] else 0)
                            if left > 0:
                                rem2[h] = left
                        rec(rem2, chosen + [(e, m)])

            rec(dict(negblk), [])
            keep = []
            for t in set(covs):
                if not any(o[0] <= t[0] and o[1] <= t[1]
                           and o != t for o in covs):
                    keep.append(t)
            cap_vars.append(keep)
    c = F(c)
    best = None
    for combo in itertools.product(*cap_vars) if cap_vars else [()]:
        Bcap = sum(t[0] for t in combo)
        u = sum(t[1] for t in combo)
        if c + u <= 0:
            continue
        bound = (K - Bcap - C) / (c + u)
        if best is None or bound > best[0]:
            best = (bound, Bcap, u)
    if best is None:
        return None
    bound, Bcap, u = best
    return {'c': c, 'u': u, 'C': C, 'K': K, 'Bcap': Bcap,
            'bound': bound, 'M': 2 * bound, 'pivot': h,
            'edges': list(edges), 'fans': dict(sorted(fans.items()))}


def block_gadgets(ctx):
    """Inequality-only gadgets per vertex: pick a subset of angle
    bounds at v.  We enumerate: cap entries B_j (dir: B=n-1-q,u=1;
    nn-comp: B=n-q,u=1; rle: B=1,u=0 on single gap) covering arcs
    that contain charged comp arcs A_i (q_{A_i} with charge
    1-q_{A_i}); bound = (sum charges - sum B)/sum u  when the cap
    ranges contain their charge arcs (sum over gaps in range >=
    sum over charge arcs).  Simplest sufficient form: enumerate
    (cap multiset, list of disjoint charge arcs each inside some
    cap), require sum_i r_{A_i} <= sum_j m_j r_{B_j} per-gap."""
    n, s = ctx.n, ctx.s
    best = None
    for v in range(s):
        caps = []
        for rng, q in ctx.dir_ang[v]:
            caps.append((frozenset(rng), F(n - 1) - q, F(1)))
        for rng, q in ctx.comp_ang[v]:
            caps.append((frozenset(rng), F(n) - q, F(1)))
        chs = []
        for rng, q in ctx.comp_ang[v]:
            if F(1) - q > 0:
                chs.append((frozenset(rng), F(1) - q))
        if not chs or not caps:
            continue
        # enumerate cap multisets of size 1..3 and disjoint charge sets
        for mcap in range(1, 4):
            for capsel in itertools.combinations_with_replacement(
                    caps, mcap):
                rngtot = {}
                for rng, B, u in capsel:
                    for g in rng:
                        rngtot[g] = rngtot.get(g, 0) + 1
                for r_ in range(1, len(chs) + 1):
                    for chsel in itertools.combinations(chs, r_):
                        need = {}
                        for rng, gn in chsel:
                            for g in rng:
                                need[g] = need.get(g, 0) + 1
                        if any(need.get(g, 0) > rngtot.get(g, 0)
                               for g in need):
                            continue
                        K = sum(gn for _, gn in chsel)
                        Bt = sum(B for _, B, _ in capsel)
                        ut = sum(u for _, _, u in capsel)
                        if ut <= 0:
                            continue
                        bound = (K - Bt) / ut
                        if best is None or bound > best[0]:
                            best = (bound, v, capsel, chsel)
    return best
