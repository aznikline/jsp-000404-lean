"""Link graph: enumerate debt chains from skeleton data alone.

Residual bookkeeping (unscaled):
  - fan_v (weight w):  w * (+r_{v,g} all g, const sum(q_v)-n, delta -1)
  - link sigma*tri{a,b,h}: const -sigma*n, delta -sigma; at each vertex
    x of the tri the angle expr contributes *sigma:
       direct arc  -> sigma*(q+r):  r +sigma, const sigma*q
       complement  -> sigma*(n+d-arc): r -sigma, const sigma*(n-q), d +sigma

Leftover r-coefficients at each vertex:
  positive part  -> optional charge: complement angle arc inside the
                    block gives min-coef * (1 - q_arc) toward K
  negative part  -> required cap: r<=1 per var, or direct-angle upper
                    bounds (joint cover or per-var)

bound = (K - Bcap - C)/(c + u),   M = 2 * bound.

Plus pure_gadget: direct angles with q_arc >= n force d >= q-(n-1)
through r >= 0 alone (degenerate caps, no equalities needed).
"""
import sys, json, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
import residual_map as rm

ZERO = F(0)


class Ctx:
    """Precomputed per-skeleton data."""

    def __init__(self, sol, n, s):
        self.sol = sol
        self.n = n
        self.s = s
        self.pos_b = []
        self.bits_b = []
        self.qs_b = []
        for v in sol:
            self.pos_b.append({d: t for t, d in enumerate(v['order'])})
            self.bits_b.append(v['bits'])
            self.qs_b.append(v['qs'])
        # all angles: ang[v][(a,b)] = (comp, frozenset rng, q)
        self.ang = []
        for x in range(s):
            d = {}
            others = [t for t in range(s) if t != x]
            for a, b in itertools.combinations(others, 2):
                rng = self.arc_rng(x, a, b)
                q = sum(self.qs_b[x][g] for g in rng)
                comp = self.bits_b[x][a] != self.bits_b[x][b]
                d[(a, b)] = (comp, frozenset(rng), q)
            self.ang.append(d)
        # per-vertex charge candidates: (gain factor base, rng)
        # gain for block coefs = min_coef_in_rng * (1 - q)
        self.comp_ang = [[(frozenset(vv[1]), vv[2])
                          for vv in self.ang[x].values() if vv[0]]
                         for x in range(s)]
        # per-vertex direct angles for caps: (rng, q)
        self.dir_ang = [[(frozenset(vv[1]), vv[2])
                         for vv in self.ang[x].values() if not vv[0]]
                        for x in range(s)]
        # signed link contributions: link[(a,b,h,sig)]
        #   -> (R_delta dict (x,g)->coef, con_delta, dcoef_delta)
        self.link = {}
        for h in range(s):
            outer = [v for v in range(s) if v != h]
            for a, b in itertools.combinations(outer, 2):
                for sig in (1, -1):
                    Rd = {}
                    con = sig * (-n)
                    dc = sig * (-1)
                    for x, u, w in ((a, b, h), (b, a, h), (h, a, b)):
                        comp, rng, q = self.ang[x][tuple(sorted((u, w)))]
                        if comp:
                            con += sig * (n - q)
                            dc += sig
                            for g in rng:
                                Rd[(x, g)] = Rd.get((x, g), 0) - sig
                        else:
                            con += sig * q
                            for g in rng:
                                Rd[(x, g)] = Rd.get((x, g), 0) + sig
                    self.link[(a, b, h, sig)] = (Rd, con, dc)
        # fan contributions: fan[v][sig] -> (Rd, con, dc)
        self.fan = {}
        for v in range(s):
            for fw in (1, -1):
                Rd = {(v, g): fw for g in range(s - 1)}
                self.fan[(v, fw)] = (Rd, fw * (sum(self.qs_b[v]) - n),
                                     -fw)

    def arc_rng(self, x, a, b):
        lo, hi = sorted((self.pos_b[x][a], self.pos_b[x][b]))
        return list(range(lo, hi))


def eval_chain(ctx, h, edges, fans):
    """edges: list of (a, b, sigma); fans: dict v -> weight ±1."""
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
            vopts = []
            mmax = max(negblk.values())
            nset = frozenset(negblk)
            for rng, q in ctx.dir_ang[v]:
                if nset <= rng:
                    vopts.append((mmax * (F(n - 1) - q), F(mmax)))
            varopts = []
            for g, m_ in negblk.items():
                chs = [(F(m_), ZERO)]
                best_cap = None
                for rng, q in ctx.dir_ang[v]:
                    if g in rng:
                        cand2 = F(n - 1) - q
                        if best_cap is None or cand2 < best_cap:
                            best_cap = cand2
                if best_cap is not None:
                    chs.append((m_ * best_cap, F(m_)))
                varopts.append(chs)
            for combo in itertools.product(*varopts):
                vopts.append((sum(t[0] for t in combo),
                              sum(t[1] for t in combo)))
            keep = []
            for t in vopts:
                if not any(o[0] <= t[0] and o[1] <= t[1]
                           and o != t for o in vopts):
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
            'bound': bound, 'M': 2 * bound,
            'pivot': h, 'edges': list(edges),
            'fans': dict(sorted(fans.items()))}


def edge_lists(perm, closed):
    """Yield sign vectors for the edge list of an open path or a
    closed cycle over `perm`."""
    base = [(perm[j - 1], perm[j]) for j in range(1, len(perm))]
    if closed and len(perm) >= 3:
        base = base + [(perm[-1], perm[0])]
    for signs in itertools.product((1, -1), repeat=len(base)):
        yield [(a, b, sg) for (a, b), sg in zip(base, signs)]


def fan_assignments(s):
    """All assignments v -> {-1,0,+1} over s vertices (as dicts)."""
    for tup in itertools.product((-1, 0, 1), repeat=s):
        yield {v: t for v, t in enumerate(tup) if t != 0}


def enumerate_max(sol, n, s):
    ctx = Ctx(sol, n, s)
    best = pure_gadget(ctx)
    fas = list(fan_assignments(s))
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for r_ in range(0, len(outer) + 1):
            perms = [()] if r_ == 0 else itertools.permutations(outer, r_)
            for perm in perms:
                for closed in (False, True):
                    for edges in edge_lists(list(perm), closed):
                        for fa in fas:
                            res = eval_chain(ctx, h, edges, fa)
                            if res is not None and (
                                    best is None or
                                    res['bound'] > best['bound']):
                                best = res
    return best


def pure_gadget(ctx):
    """Degenerate caps: direct angle with q_arc >= n gives
    arc <= (n-1-q)+d, i.e. d >= q-(n-1) via r >= 0.
    Disjoint-arc caps may stack: bound = sum(q_j-(n-1)) / m."""
    n, s = ctx.n, ctx.s
    cand = []
    for v in range(s):
        for rng, q in ctx.dir_ang[v]:
            if q >= n:
                cand.append((F(q - (n - 1)), v, rng))
    if not cand:
        return None
    best = None
    for m in range(1, len(cand) + 1):
        for sel in itertools.combinations(cand, m):
            ok = True
            for i in range(len(sel)):
                for j in range(i + 1, len(sel)):
                    if sel[i][1] == sel[j][1] and sel[i][2] & sel[j][2]:
                        ok = False
            if not ok:
                continue
            bnd = sum(t[0] for t in sel) / m
            if best is None or bnd > best[0]:
                best = (bnd, sel)
    if best is None:
        return None
    bnd, sel = best
    return {'c': ZERO, 'u': F(len(sel)), 'C': ZERO, 'K': ZERO,
            'Bcap': -sum(t[0] for t in sel), 'bound': bnd,
            'M': 2 * bnd, 'pivot': None, 'edges': [],
            'fans': {}, 'pure': True, 'caps': sel}


def lp_level(E, sol, n):
    E.ORIG.clear()
    b = E.build_case(sol, n, 'A')
    ineqs, eqs = b
    ineqs = E.substitute(eqs, ineqs)
    st, lo, y = rm.glp_min_delta(ineqs, E.CONST, E.DELTA)
    return st, lo


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 's4'
    filt = sys.argv[2] if len(sys.argv) > 2 else ''
    if which == 's4':
        import skeleton_enum as sen
        E = rm.load_s4()
        n = s = 4
        dd = json.load(open('chain_dump_s4.json'))
        VV = sen.build_VV((3, 2, 2, 1), n)
        build = lambda r: [VV[v][r['idxs'][v]] for v in range(s)]
    else:
        import generic_enum as ge
        E = rm.load_g()
        n = s = 5
        dd = json.load(open('chain_dump_s5.json'))
        cache = {}
        def build(r):
            fn = r['tag'].split(':')[0]
            if fn not in cache:
                ks = json.load(open(fn))['ks']
                cache[fn] = ge.build_VV(ks, n, s)
            VV = cache[fn]
            return [VV[v][r['idxs'][v]] for v in range(s)]
    okc = bad = 0
    for rec in dd:
        if filt and filt not in rec['tag']:
            continue
        sol = build(rec)
        best = enumerate_max(sol, n, s)
        st, lo = lp_level(E, sol, n)
        bb = None if best is None else best['bound']
        match = (bb is not None and lo is not None and bb >= lo)
        if match:
            okc += 1
        else:
            bad += 1
        print(f"{rec['tag'][:44]:46s} LP={st}:{lo} "
              f"best={None if best is None else (bb, 'h='+str(best['pivot']), best['edges'], best['fans'], 'M='+str(best['M']))}",
              flush=True)
    print(f'match(best>=LP) {okc}/{okc+bad}')


if __name__ == '__main__':
    main()
