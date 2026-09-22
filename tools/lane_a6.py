"""Extended gadget evaluator v2.

Per-vertex cap semantics (general): the negative residual block N at v
(coefs kap_g>0 meaning residual -kap_g r_g; N may be empty) is bounded
by a subset S of v's primitive upper/lower bound entries:

  upper:  r_g <= 1                        (const 1, dcoef 0, coef e_g)
          sum_A r <= capA + delta         (angle upper bound; direct arc
                                           const n-1-qA, comp arc const
                                           n-qA; dcoef 1)
  lower:  -sum_B r <= qB - 1              (comp angle bound; dcoef 0)

Coverage: alpha_g := sum_S coef_g >= kap_g for g in N and >= 0 off N
(the off-N positive part is absorbed by r >= 0).  Cost = (C,u) =
(sum const, sum dcoef).  Empty N allows 'floor' certificates C<0.

Each primitive inequality usable once; upper entries duplicated to
allow covering kap>1.
"""
import sys, itertools, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import link_graph as lg

ZERO = F(0)


def vertex_entries(ctx, v, mult=2):
    """Primitive bound entries at v: (coef tuple, const, dcoef)."""
    n, s = ctx.n, ctx.s
    m = s - 1
    ents = []
    for g in range(m):
        c = [0] * m
        c[g] = 1
        for _ in range(mult):
            ents.append((tuple(c), F(1), 0))          # r_g <= 1
    for (rng, q) in ctx.dir_ang[v]:
        c = [1 if g in rng else 0 for g in range(m)]
        for _ in range(mult):
            ents.append((tuple(c), F(n - 1) - q, 1))  # sum_A r <= cap+d
    for (rng, q) in ctx.comp_ang[v]:
        c = [1 if g in rng else 0 for g in range(m)]
        for _ in range(mult):
            ents.append((tuple(c), F(n) - q, 1))      # comp upper
        c = [-1 if g in rng else 0 for g in range(m)]
        ents.append((tuple(c), q - 1, 0))             # comp lower
    return ents


_CAP_CACHE = {}


def cap_options_ext(ctx, v, negblk, maxsz=5):
    """Pareto-optimal (C,u) for covering negblk {gap: mag} at v.
    negblk={} -> floor certificates allowed."""
    key = (id(ctx), v, tuple(sorted(negblk.items())), maxsz)
    if key in _CAP_CACHE:
        return _CAP_CACHE[key]
    res = _cap_options_uncached(ctx, v, negblk, maxsz)
    _CAP_CACHE[key] = res
    return res


def _cap_options_uncached(ctx, v, negblk, maxsz=5):
    m = ctx.s - 1
    maxk = max(negblk.values()) if negblk else 0
    ents = vertex_entries(ctx, v, mult=max(1, min(maxk, 3)))
    ne = len(ents)
    out = []
    for sz in range(0, min(maxsz, ne) + 1):
        for S in itertools.combinations(range(ne), sz):
            alpha = [0] * m
            C = ZERO
            u = 0
            for e in S:
                cf, cc, dd = ents[e]
                for g in range(m):
                    alpha[g] += cf[g]
                C += cc
                u += dd
            ok = True
            for g in range(m):
                if alpha[g] < negblk.get(g, 0):
                    ok = False
                    break
            if ok:
                out.append((C, F(u)))
    keep = []
    for t in out:
        if not any(o[0] <= t[0] and o[1] <= t[1] and o != t
                   for o in out):
            keep.append(t)
    return keep


def eval_chain_ext(ctx, h, edges, fans, maxsz=5):
    n, s = ctx.n, ctx.s
    R = {}
    con = ZERO
    dc = 0
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
        # generalized cap/floor options at EVERY vertex
        if negblk:
            cap_vars.append(cap_options_ext(ctx, v, negblk, maxsz))
        else:
            floor_opts = [(ZERO, ZERO)] + [
                o for o in cap_options_ext(ctx, v, {}, maxsz)
                if o[0] < 0]
            if len(floor_opts) > 1:
                cap_vars.append(floor_opts)

    c = F(c)
    best = None
    for combo in itertools.product(*cap_vars) if cap_vars else [()]:
        Bcap = sum(t[0] for t in combo)
        u = sum(t[1] for t in combo)
        if c + u <= 0:
            continue
        bound = (K - Bcap - C) / (c + u)
        if best is None or bound > best:
            best = bound
    return best


def enumerate_max_ext(sol, n, s, maxsz=5, target=None):
    """Best extended-cap gadget bound; early-exits once best >= target."""
    ctx = lg.Ctx(sol, n, s)
    best = None
    pg = lg.pure_gadget(ctx)
    if pg is not None:
        best = pg['bound']
    if target is not None and best is not None and best >= target:
        return best
    fas = list(lg.fan_assignments(s))
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for r_ in range(0, len(outer) + 1):
            perms = [()] if r_ == 0 else itertools.permutations(outer, r_)
            for perm in perms:
                for closed in (False, True):
                    for edges in lg.edge_lists(list(perm), closed):
                        for fa in fas:
                            b = eval_chain_ext(ctx, h, edges, fa, maxsz)
                            if b is not None and (
                                    best is None or b > best):
                                best = b
                                if target is not None and best >= target:
                                    return best
    return best
