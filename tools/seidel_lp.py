"""Seidel-style incremental LP (float), small dimension.

maximize c·x  s.t.  a_i·x ≤ b_i

State between constraints is either a finite point x* or an unbounded
ray (x0, d).  When x* violates the new constraint h, the optimum of
the processed set lies on h's boundary → eliminate one variable and
recurse on the boundary sub-LP.

Bounds for every variable are processed FIRST (deterministically) so
that after them x* is a finite point; the remaining constraints are
then shuffled (randomized incremental).

Returns ('infeasible',) | ('unbounded',) | ('bounded', opt_value, x).
"""
import random

EPS = 1e-9

def _dot(a, x):
    return sum(av * xv for av, xv in zip(a, x))

def _solve1(c, cons):
    """1-var LP: maximize c·x s.t. a·x ≤ b.
    Returns ('infeasible',) | ('bounded', val, x) | ('unbounded', x0, d)
    """
    lo, hi = -1e100, 1e100
    for a, b in cons:
        a = a[0]
        if a > EPS:
            hi = min(hi, b / a)
        elif a < -EPS:
            lo = max(lo, b / a)
        elif b < -EPS:
            return ('infeasible',)
    if lo > hi + 1e-7:
        return ('infeasible',)
    if c > EPS:
        if hi > 1e90:
            return ('unbounded', [max(lo, -1e6)], [1.0])
        return ('bounded', c * hi, [hi])
    if c < -EPS:
        if lo < -1e90:
            return ('unbounded', [min(hi, 1e6)], [-1.0])
        return ('bounded', c * lo, [lo])
    x0 = min(max(0.0, lo), hi) if hi < 1e90 else max(lo, 0.0)
    return ('bounded', 0.0, [x0])

def _elim(nv, cons, obj, a_h, b_h, v):
    """Restrict to hyperplane a_h·x = b_h, eliminating variable v.
    Returns (ncons, nobj, const, embed) where embed maps a reduced
    vector (nv-1 comps) to the full vector (nv comps)."""
    ahv = a_h[v]
    ncons = []
    for a, b in cons:
        if abs(a[v]) < EPS:
            ncons.append((a[:v] + a[v + 1:], b))
        else:
            f = a[v] / ahv
            na = [a[u] - f * a_h[u] for u in range(nv) if u != v]
            ncons.append((na, b - f * b_h))
    if abs(obj[v]) < EPS:
        nobj = obj[:v] + obj[v + 1:]
        const = 0.0
    else:
        f = obj[v] / ahv
        nobj = [obj[u] - f * a_h[u] for u in range(nv) if u != v]
        const = f * b_h
    def embed(xr):
        x = list(xr)
        xv = (b_h - sum(a_h[u] * (x[u] if u < v else x[u - 1])
                        for u in range(nv) if u != v)) / ahv
        x.insert(v, xv)
        return x
    return ncons, nobj, const, embed

def _rec(nv, cons, obj):
    """Core recursion over a constraint list (already ordered)."""
    if nv == 1:
        return _solve1(obj[0], cons)
    # x* state: ('ray', x0, d) or ('pt', x)
    cur = ('ray', [0.0] * nv, list(obj))
    for i, (a, b) in enumerate(cons):
        if cur[0] == 'pt':
            x = cur[1]
            if _dot(a, x) <= b + 1e-7:
                continue
        else:
            _, x0, d = cur
            ad = _dot(a, d)
            if ad < -EPS or (abs(ad) <= EPS
                             and _dot(a, x0) <= b + 1e-7):
                continue                        # ray survives h
        # restrict to boundary a·x = b
        v = max(range(nv), key=lambda u: abs(a[u]))
        if abs(a[v]) < EPS:
            if b < -EPS:
                return ('infeasible',)
            continue
        ncons, nobj, const, embed = _elim(nv, cons[:i], obj, a, b, v)
        r = _rec(nv - 1, ncons, nobj)
        if r[0] == 'infeasible':
            return ('infeasible',)
        if r[0] == 'unbounded':
            # lift the reduced ray (x0', d') to full space
            x0f = embed(r[1])
            df = embed([x + y for x, y in zip(r[1], r[2])])
            d = [df[u] - x0f[u] for u in range(nv)]
            cur = ('ray', x0f, d)
        else:
            cur = ('pt', embed(r[2]))
    if cur[0] == 'pt':
        return ('bounded', _dot(obj, cur[1]), cur[1])
    # degenerate ray: direction ≈ 0 means the optimum is really a point
    if max(map(abs, cur[2])) <= 1e-7:
        return ('bounded', _dot(obj, cur[1]), cur[1])
    return ('unbounded', cur[1], cur[2])

def lp_max(nv, cons, obj, bounds=None):
    """cons: [(a,b)];  obj: c.  bounds: list of (lo,hi) per var,
    processed deterministically first (use None entries to skip)."""
    ordered = []
    if bounds:
        for v, bd in enumerate(bounds):
            if bd is None:
                continue
            lo, hi = bd
            if hi is not None:
                a = [0.0] * nv
                a[v] = 1.0
                ordered.append((a, float(hi)))
            if lo is not None:
                a = [0.0] * nv
                a[v] = -1.0
                ordered.append((a, -float(lo)))
    rest = list(cons)
    random.shuffle(rest)
    ordered += rest
    return _rec(nv, ordered, obj)
