"""Lane-E challenger utilities.

Shared helpers for adversarial hunts against
  T_low : consistent skeleton + W > 2   => exists gadget level >= 1
  T_high: consistent skeleton + W > 5/2 => exists gadget level >= 2

"Level >= m" operationalized as LP min-delta >= m/2 on a
mode-A-consistent (LP-feasible) skeleton; the gadget side is checked
with link_graph.enumerate_max (possibly budget-limited).
"""
import sys, itertools, random
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_model as gm
import generic_enum as ge
import generic_cegis as gce
import residual_map as rm
import link_graph as lg

ZERO, ONE = F(0), F(1)


# ---------------------------------------------------------------------
# variant / signature construction (mirrors generic_model, but lets us
# build a single variant dict directly from (order, bits, qs))
# ---------------------------------------------------------------------

def mk_variant(vi, order, bits, qs, n):
    """Build a variant dict identical in shape to
    generic_model.vertex_variants output, for one explicit
    (order, bits, qs) triple.  `bits` maps vertex-label -> 0/1."""
    others = list(order)
    m = len(others)
    pos = {d: t for t, d in enumerate(order)}
    gaps = [gm.add(gm.mk(qs[t]), gm.var(('r', vi, t)))
            for t in range(m)]

    def arc(a, b):
        e = gm.mk(0)
        for t in range(min(a, b), max(a, b)):
            e = gm.add(e, gaps[t])
        return e

    arcs, angles, side = {}, {}, {}
    for u, v in itertools.combinations(others, 2):
        a_ = arc(pos[u], pos[v])
        arcs[frozenset((u, v))] = a_
        if bits[u] == bits[v]:
            angles[frozenset((u, v))] = a_
        else:
            angles[frozenset((u, v))] = gm.add(
                gm.add(gm.mk(n), gm.var(gm.DELTA)), a_, -ONE)
    for j in others:
        for k in others:
            if k == j:
                continue
            sgn = 1 if pos[k] > pos[j] else -1
            if bits[k] != bits[j]:
                sgn = -sgn
            side[(j, k)] = sgn
    return dict(v=vi, order=tuple(order), bits=dict(bits), qs=tuple(qs),
                gaps=gaps, arcs=arcs, angles=angles, side=side)


def sig_keys(v, s):
    """All (order, bits) signatures at vertex v, with side dicts."""
    others = tuple(x for x in range(s) if x != v)
    out = []
    for order in itertools.permutations(others):
        pos = {d: t for t, d in enumerate(order)}
        for bb in itertools.product((0, 1), repeat=s - 2):
            bits = dict(zip(order[1:], bb))
            bits[order[0]] = 0
            side = {}
            for j in others:
                for k in others:
                    if k == j:
                        continue
                    sgn = 1 if pos[k] > pos[j] else -1
                    if bits[k] != bits[j]:
                        sgn = -sgn
                    side[(j, k)] = sgn
            out.append((order, tuple(sorted(bits.items())), side))
    return out


def edge_ok_sig(si, sj, i, j, s):
    """Signature-level edge consistency between sig si at vertex i and
    sig sj at vertex j (generic_enum.consistent on raw signatures)."""
    side_i, side_j = si[2], sj[2]
    for k in range(s):
        if k == i or k == j:
            continue
        if side_i[(j, k)] != -side_j[(i, k)]:
            return False
    return True


# ---------------------------------------------------------------------
# LP wrappers
# ---------------------------------------------------------------------

def build_ineqs(sol, n, skip=frozenset()):
    gm.ORIG.clear()
    b = gm.build_case(sol, n, 'A', skip=skip)
    if b is None:
        return None
    ineqs, eqs = b
    return gm.substitute(eqs, ineqs)


def lp_f(sol, n):
    ineqs = build_ineqs(sol, n)
    if ineqs is None:
        return ('buildfail', None)
    return gce.lp_min_delta_f(ineqs)


def lp_x(sol, n):
    """Exact Fraction LP.  Returns (status, Fraction-or-None)."""
    ineqs = build_ineqs(sol, n)
    if ineqs is None:
        return ('buildfail', None)
    st, lo, y = rm.glp_min_delta(ineqs, gm.CONST, gm.DELTA)
    return (st, lo)


def lp_min_delta_free(ineqs):
    """Float LP min-delta with NO implicit variable bounds.

    NOTE: generic_cegis.lp_min_delta_f passes bounds [(0,1)] to
    seidel_lp.lp_max, which clamps delta to [0,1] *regardless* of the
    skip list — making its 'relaxed' variants silently capped.  This
    version passes bounds=None: r-vars stay bounded by the explicit
    r>=0 / r<=1 inequalities; delta is free (>=0 and <1 only if the
    corresponding constraints are present)."""
    import seidel_lp
    present = sorted({v for q in ineqs for v in q.a
                      if v != gm.CONST}, key=str)
    if gm.DELTA not in present:
        present.append(gm.DELTA)
    idx = {v: t for t, v in enumerate(present)}
    nv = len(present)
    cons = [([float(q.a.get(v, 0)) for v in present],
             float(q.b) - float(q.a.get(gm.CONST, 0)))
            for q in ineqs]
    obj = [0.0] * nv
    obj[idx[gm.DELTA]] = -1.0
    r = seidel_lp.lp_max(nv, cons, obj, None)
    if r[0] == 'infeasible':
        return ('infeasible', None)
    if r[0] == 'unbounded':
        return ('unbounded', None)
    return ('bounded', -r[1])


def lp_f_free(sol, n):
    """Float LP with δ completely free (no δ>=0, no δ<1).

    Under Lean ModeA semantics (no delta hypothesis), feasibility of
    this system IS skeleton consistency.  A skeleton feasible only at
    delta < 0 has gadget-bound ceiling < 0 -> no level>=1 gadget can
    exist (any valid gadget bound <= min feasible delta)."""
    gm.ORIG.clear()
    b = gm.build_case(sol, n, 'A', skip={'δ<1', 'δ≥0'})
    if b is None:
        return ('buildfail', None)
    ineqs, eqs = b
    ineqs = gm.substitute(eqs, ineqs)
    return lp_min_delta_free(ineqs)


def lp_f_relaxed(sol, n):
    """Float min-delta WITHOUT the δ<1 cap (δ>=0 retained).

    Value <= 1  <=>  capped LP feasible (mode-A consistent).
    Value in (1, inf)  <=>  'inf' skeleton that is really a
    high-debt case (a gadget of that level exists in principle).
    infeasible  <=>  structurally inconsistent for all delta."""
    gm.ORIG.clear()
    b = gm.build_case(sol, n, 'A', skip={'δ<1'})
    if b is None:
        return ('buildfail', None)
    ineqs, eqs = b
    ineqs = gm.substitute(eqs, ineqs)
    return lp_min_delta_free(ineqs)


def lp_relaxed(sol, n, delta_hi=None):
    """Min-delta LP with the 'δ<1' cap removed (or raised).
    Tests whether an 'inf' skeleton is truly inconsistent or merely
    needs delta >= 1.  delta_hi=None removes the bound entirely."""
    gm.ORIG.clear()
    b = gm.build_case(sol, n, 'A', skip={'δ<1'})
    if b is None:
        return ('buildfail', None)
    ineqs, eqs = b
    ineqs = gm.substitute(eqs, ineqs)
    if delta_hi is not None:
        a = {gm.CONST: ZERO, gm.DELTA: ONE}
        ineqs.append(gm.C(a, F(delta_hi), {}))
    return rm.glp_min_delta(ineqs, gm.CONST, gm.DELTA)


# ---------------------------------------------------------------------
# profiles / W
# ---------------------------------------------------------------------

def deficit_profiles(n, s):
    """All non-decreasing deficit tuples d_i in [0, n-1] (k_i>=0)."""
    out = []

    def rec(pos, lo, cur):
        if pos == s:
            out.append(tuple(cur))
            return
        for d in range(lo, n):
            cur.append(d)
            rec(pos + 1, d, cur)
            cur.pop()

    rec(0, 0, [])
    return out


def W_of_d(d):
    return sum(F(1, 2) ** x for x in d)


def ks_of_d(n, d):
    return [n - 1 - x for x in d]


# ---------------------------------------------------------------------
# skeleton (de)serialization for fixtures
# ---------------------------------------------------------------------

def sol_to_data(sol):
    return [{'order': list(v['order']),
             'bits': {str(k): b for k, b in v['bits'].items()},
             'qs': list(v['qs'])} for v in sol]


def data_to_sol(data, n):
    return [mk_variant(v, tuple(d['order']),
                       {int(k): b for k, b in d['bits'].items()},
                       tuple(d['qs']), n)
            for v, d in enumerate(data)]


# ---------------------------------------------------------------------
# randomized consistent-signature sampler (s-generic)
# ---------------------------------------------------------------------

class Sampler:
    """Randomized consistent-signature + q-leaf sampler."""

    def __init__(self, ks, n, s, rng=None):
        self.ks, self.n, self.s = ks, n, s
        self.rng = rng or random.Random()
        self.siglists = [sig_keys(v, s) for v in range(s)]
        self.qlists = [sorted(gm.q_tuples(ks[v], n, s - 1))
                       for v in range(s)]
        self.tris = list(itertools.combinations(range(s), 3))
        self.tris_by_v = [[] for _ in range(s)]
        for t in self.tris:
            self.tris_by_v[max(t)].append(t)

    def rand_sig_tuple(self, tries_per_v=400, restarts=200):
        """Random consistent signature tuple via restart-greedy."""
        s = self.s
        rng = self.rng
        for _ in range(restarts):
            chosen = [None] * s
            ok = True
            for v in range(s):
                lst = self.siglists[v]
                found = None
                for _ in range(tries_per_v):
                    cand = lst[rng.randrange(len(lst))]
                    if all(edge_ok_sig(cand, chosen[u], v, u, s)
                           for u in range(v)):
                        found = cand
                        break
                if found is None:
                    ok = False
                    break
                chosen[v] = found
            if ok:
                return chosen
        return None

    def rand_qs_tuple(self, sigt, tries=60):
        """Random q leaves for a fixed signature tuple; checks
        tri_maybe incrementally.  Returns qs list or None."""
        s, n, rng = self.s, self.n, self.rng
        order_v = list(range(s))
        rng.shuffle(order_v)
        qs_ch = [None] * s
        sol_part = [None] * s
        for v in order_v:
            ql = self.qlists[v]
            ordr, bitsk, _ = sigt[v]
            bits = dict(bitsk)
            placed = False
            for _ in range(tries):
                qs = ql[rng.randrange(len(ql))]
                vv = mk_variant(v, ordr, bits, qs, n)
                sol_part[v] = vv
                okk = True
                for t in self.tris:
                    if v in t and all(sol_part[x] is not None
                                      for x in t):
                        if not gm.tri_maybe(t, sol_part, n):
                            okk = False
                            break
                if okk:
                    qs_ch[v] = qs
                    placed = True
                    break
            sol_part[v] = None if not placed else sol_part[v]
            if not placed:
                return None
        return qs_ch

    def sample(self, ntries_sig=200, q_tries=60, sig_tries=400):
        """One random skeleton (consistent sigs + tri_maybe leaves),
        or None."""
        sigt = self.rand_sig_tuple(tries_per_v=sig_tries,
                                   restarts=ntries_sig)
        if sigt is None:
            return None
        qs = self.rand_qs_tuple(sigt, tries=q_tries)
        if qs is None:
            return None
        sol = [mk_variant(v, sigt[v][0], dict(sigt[v][1]), qs[v],
                          self.n)
               for v in range(self.s)]
        return sol
