"""s-generic remainder/cell model for the Sendov Section-4 contract.

Same semantics as remainder_check.py (s=4) but parametrized by s
(number of vertices).  Each vertex i has m = s-1 fan directions, m
gaps, arcs between direction pairs, and side assignments for the
s-2 third vertices of each incident edge.

Constraint objects carry an explicit (kind, key) so downstream
layers (LP, MUS, Farkas extraction, mode-B leak audit) never see s.

Mode B is intentionally NOT implemented here — it is a frozen
negative control and lives only in the s=4 checker.
"""
from fractions import Fraction as F
from itertools import permutations, combinations, product

ZERO, ONE = F(0), F(1)
CONST = 'c'
DELTA = 'δ'

def var(v):        return {CONST: ZERO, v: ONE}
def mk(c):         return {CONST: F(c)}
def add(e, o, w=ONE):
    out = dict(e)
    for k, c in o.items():
        out[k] = out.get(k, ZERO) + w * c
        if out[k] == 0 and k != CONST:
            del out[k]
    return out
def neg(e):        return {k: -c for k, c in e.items()}

def q_tuples(ktarget, n, m):
    """m gap cells: exponent Σ max(q-1,0) = ktarget, Σq ≤ n."""
    out = set()
    for qs in product(range(n + 1), repeat=m):
        if (sum(max(q - 1, 0) for q in qs) == ktarget
                and sum(qs) <= n):
            out.add(qs)
    return sorted(out)

def vertex_variants(vi, ktarget, others, n):
    """Local skeletons at vertex vi for general fan size m=len(others).

    Variant = (order, bits, qs):
      order: cyclic fan order of the m other vertices on the
             projective π-circle;
      bits:  2π-lift (ray orientation), order[0] fixed to 0;
      qs:    integer cells of the m cyclic gaps.
    """
    m = len(others)
    out = []
    for order in permutations(others):
        pos = {d: t for t, d in enumerate(order)}
        for bb in product((0, 1), repeat=m - 1):
            bits = dict(zip(order[1:], bb))
            bits[order[0]] = 0
            for qs in q_tuples(ktarget, n, m):
                gaps = [add(mk(qs[t]), var(('r', vi, t)))
                        for t in range(m)]

                def arc(a, b, pos=pos, gaps=gaps):
                    e = mk(0)
                    for t in range(min(a, b), max(a, b)):
                        e = add(e, gaps[t])
                    return e

                arcs, angles, side = {}, {}, {}
                for u, v in combinations(others, 2):
                    a_ = arc(pos[u], pos[v])
                    arcs[frozenset((u, v))] = a_
                    if bits[u] == bits[v]:
                        angles[frozenset((u, v))] = a_
                    else:
                        # projective complement  π − arc = n+δ − arc
                        angles[frozenset((u, v))] = add(
                            add(mk(n), var(DELTA)), a_, -ONE)
                for j in others:
                    for k in others:
                        if k == j:
                            continue
                        sgn = 1 if pos[k] > pos[j] else -1
                        if bits[k] != bits[j]:
                            sgn = -sgn
                        side[(j, k)] = sgn
                out.append(dict(v=vi, order=order, bits=bits, qs=qs,
                                gaps=gaps, arcs=arcs, angles=angles,
                                side=side))
    return out

# ---------------------------------------------------------------------
# constraints
# ---------------------------------------------------------------------

class Constraint:
    """form = 0 (equality) or form ≤ 0 (inequality)."""
    __slots__ = ('kind', 'key', 'desc', 'form', 'is_eq')

    def __init__(self, kind, key, desc, form, is_eq):
        self.kind = kind
        self.key = key
        self.desc = desc
        self.form = {k: v for k, v in form.items()
                     if v != 0 or k == CONST}
        self.is_eq = is_eq

ORIG = []
def oreg(kind, key, desc, form, is_eq):
    ORIG.append(Constraint(kind, key, desc, form, is_eq))
    return len(ORIG) - 1

class C:
    """LP inequality a·x ≤ b with provenance {orig_id: coeff}."""
    __slots__ = ('a', 'b', 'p')
    def __init__(self, a, b, p):
        self.a = {k: v for k, v in a.items() if v != 0 or k == CONST}
        self.b = F(b)
        self.p = {k: v for k, v in p.items() if v != 0}

MARGIN = 'M'

def build_case(vs, n, mode='A', skip=frozenset(), strict=False):
    """vs: list of s variant dicts.  Returns (ineqs, eqs) or None.

    strict=True replaces the box bounds r<=1, delta<=1 by r<=M, delta<=M
    (M>=0 added).  min M < 1 over this system is *exactly* strict
    feasibility 0<=r<1, 0<=delta<1: the margin LP needs no epsilon.
    """
    if mode != 'A':
        raise NotImplementedError('mode B frozen; s=4 only '
                                  '(remainder_check.py)')
    s = len(vs)
    ineqs, eqs = [], []

    def I(kind, key, desc, expr, b):
        if desc in skip:
            return
        cid = oreg(kind, key, desc, add(expr, mk(-b)), False)
        ineqs.append(C(expr, b, {cid: ONE}))

    def E(kind, key, desc, expr, rhs):
        if desc in skip:
            return
        cid = oreg(kind, key, desc, add(expr, mk(-rhs)), True)
        eqs.append([expr, F(rhs), {cid: ONE}])

    m = s - 1
    for vi in range(s):
        for g in range(m):
            rv = ('r', vi, g)
            I('rnn', (vi, g), f'r{vi}{g}≥0', neg(var(rv)), ZERO)
            if strict:
                I('rle', (vi, g), f'r{vi}{g}≤M',
                  add(var(rv), var(MARGIN), -ONE), ZERO)
            else:
                I('rle', (vi, g), f'r{vi}{g}≤1', var(rv), ONE)
    I('delta', 'lo', 'δ≥0', neg(var(DELTA)), ZERO)
    if strict:
        I('delta', 'hi', 'δ≤M', add(var(DELTA), var(MARGIN), -ONE), ZERO)
        I('margin', 'lo', 'M≥0', neg(var(MARGIN)), ZERO)
    else:
        I('delta', 'hi', 'δ<1', var(DELTA), ONE)
    for vi in range(s):
        e = mk(0)
        for ge in vs[vi]['gaps']:
            e = add(e, ge)
        e = add(e, var(DELTA), -ONE)          # Σgaps − δ = n
        E('fan', vi, f'V{vi} Σgap=π', e, n)
    for tri in combinations(range(s), 3):
        i, j, k = tri
        e = add(vs[i]['angles'][frozenset((j, k))],
                vs[j]['angles'][frozenset((i, k))])
        e = add(e, vs[k]['angles'][frozenset((i, j))])
        e = add(e, var(DELTA), -ONE)          # A+B+C − δ = n
        E('tri', tri, f'Δ{tri} Σ=π', e, n)
    for i in range(s):
        oth = [x for x in range(s) if x != i]
        for u, v in combinations(oth, 2):
            a = vs[i]['angles'][frozenset((u, v))]
            # provable contract:  angle ≤ n+δ−1  (∠ ≤ π−λ)
            I('ang', (i, u, v), f'∠{i}{u}{v}≤π−λ',
              add(a, var(DELTA), -ONE), n - 1)
            # trivial angle nonnegativity (mode A member)
            I('ange', (i, u, v), f'∠{i}{u}{v}≥0', neg(a), ZERO)
    for vi in range(s):
        for gi, ge in enumerate(vs[vi]['gaps']):
            I('gnn', (vi, gi), f'g{vi}{gi}≥0', neg(ge), ZERO)
    return ineqs, eqs

# ---------------------------------------------------------------------
# provenance-aware equality substitution (same algorithm as
# remainder_check.substitute, operating on this module's objects)
# ---------------------------------------------------------------------

def substitute(eqs, ineqs):
    eqs = [[dict(e), r, dict(p)] for e, r, p in eqs]
    while True:
        idx = None
        for t, (e, rhs, p) in enumerate(eqs):
            if any(v not in (CONST, DELTA) and c != 0
                   for v, c in e.items()):
                idx = t
                break
        if idx is None:
            break
        e, rhs, p = eqs.pop(idx)
        piv = next(v for v, c in e.items()
                   if v not in (CONST, DELTA) and c != 0)
        cp = e[piv]
        rest = dict(e)
        rest.pop(piv)
        expr = {k: -c / cp for k, c in rest.items()}
        expr[CONST] = expr.get(CONST, ZERO) + rhs / cp
        provE = {k: c / cp for k, c in p.items()}

        def subst(A, pv):
            if piv not in A:
                return A, pv
            c = A.pop(piv)
            for k, cc in expr.items():
                A[k] = A.get(k, ZERO) + c * cc
                if A[k] == 0 and k != CONST:
                    del A[k]
            pv2 = dict(pv)
            for k, cc in provE.items():
                pv2[k] = pv2.get(k, ZERO) - c * cc
            return A, pv2

        for iq in ineqs:
            iq.a, iq.p = subst(iq.a, iq.p)
        for t in eqs:
            t[0], t[2] = subst(t[0], t[2])
    for e, rhs, p in eqs:
        ineqs.append(C(e, rhs, p))
        ineqs.append(C(neg(e), -rhs,
                       {k: -c for k, c in p.items()}))
    return ineqs

def extract_cert(ineqs_sub, y):
    """Dual weights → provenance over ORIG.  Returns (W, combo)."""
    W = {}
    for j, w in enumerate(y):
        if w == 0:
            continue
        for cid, c in ineqs_sub[j].p.items():
            W[cid] = W.get(cid, ZERO) + w * c
    combo = {}
    for cid, w in W.items():
        if w == 0:
            continue
        con = ORIG[cid]
        if not con.is_eq and w < 0:
            return None
        for k, c in con.form.items():
            combo[k] = combo.get(k, ZERO) + w * c
    return W, combo

def tri_maybe(tri, vs, n):
    i, j, k = tri
    e = add(vs[i]['angles'][frozenset((j, k))],
            vs[j]['angles'][frozenset((i, k))])
    e = add(e, vs[k]['angles'][frozenset((i, j))])
    c = e.get(CONST, ZERO)
    dc = e.get(DELTA, ZERO)
    rmin = rmax = ZERO
    for v, a in e.items():
        if v in (CONST, DELTA):
            continue
        if a > 0:
            rmax += a
        else:
            rmin += a
    lo = (n - c) + min(ZERO, ONE - dc)
    hi = (n - c) + max(ZERO, ONE - dc)
    return lo <= rmax and hi >= rmin
