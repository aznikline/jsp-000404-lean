"""Exact remainder (carry) feasibility checker for s=4 cell witnesses.

For each fan gap g at vertex v: angle/λ = m_{v,g} + r_{v,g},
  m integer cell, r in [0,1) remainder.  pi/lambda = u/2 = n + delta.

Exact equalities (affine in delta):
  VERT_v : sum_g r_{v,g} = n+δ - C_v          (fan sums to pi)
  TRI_T  : sum over 3 interior blocks = n+δ - C_T  (triangle sums to pi)
Inequalities:
  BLK_{v,B} : block sum <= n+δ-1 - C_B        (interior angle <= 1-2/u)
  POS_g : r_g >= 0 ;  LT1_g : r_g <= 1        (0 <= r < 1, weak form)

Method: Gauss-eliminate the 8 equalities over Q (RHS affine in δ),
substitute into inequalities -> small system in ~4 free vars, then
Fourier-Motzkin with provenance labels -> Farkas certificate.
All arithmetic exact (Fraction); δ kept symbolic as affine pair (c0,c1).
"""

import itertools
from fractions import Fraction as Fr

# ---------- affine-in-delta bounds: (c0, c1) = c0 + c1*delta ----------
def badd(a, b): return (a[0] + b[0], a[1] + b[1])
def bscale(a, k): return (a[0] * k, a[1] * k)
def bneg(a): return (-a[0], -a[1])
def bval(a, delta): return a[0] + a[1] * Fr(delta).limit_denominator(10**6)

# ---------- linear expressions: (const:(c0,c1), {var:Fraction}) ----------
def expr_add(e1, e2):
    c = dict(e1[1])
    for v, k in e2[1].items():
        c[v] = c.get(v, Fr(0)) + k
    return (badd(e1[0], e2[0]), {v: k for v, k in c.items() if k != 0})
def expr_scale(e, k):
    return (bscale(e[0], k), {v: kk * k for v, kk in e[1].items()})
def expr_var(v): return ((Fr(0), Fr(0)), {v: Fr(1)})
def expr_const(c0, c1=0): return ((Fr(c0), Fr(c1)), {})

# ---------- equalities as (coefs {var:Fr}, rhs (c0,c1), label) ----------
def gauss_solve(eqs, nvars):
    """eqs: list of ({var:Fr}, rhs, label). Returns dict var -> expr over
    free vars + cert contributions {label:coef} per eliminated var."""
    # rows: coef dict; we'll pivot greedily
    rows = []
    for (co, rhs, lab) in eqs:
        rows.append((dict(co), rhs, lab))
    pivots = {}   # var -> (coef dict, rhs, label)  normalized
    for (co, rhs, lab) in rows:
        co = dict(co)
        # reduce by existing pivots
        for pv in list(co.keys()):
            if pv in pivots and co.get(pv, 0) != 0:
                k = co[pv]
                pco, prhs, plab = pivots[pv]
                for v, kk in pco.items():
                    if v == pv: continue
                    co[v] = co.get(v, Fr(0)) - k * kk
                co[pv] = Fr(0)
                rhs = badd(rhs, bneg(bscale(prhs, k)))
                # (label bookkeeping handled later via substitution certs)
        # find a pivot var
        pv = next((v for v, k in co.items() if k != 0), None)
        if pv is None:
            continue  # dependent or inconsistent (assume consistent)
        k = co[pv]
        for v in list(co.keys()):
            co[v] /= k
        rhs = bscale(rhs, Fr(1) / k)
        pivots[pv] = (co, rhs, lab)
    # solution: pivot var = rhs - sum_{free} coef*free.
    # Pivot expressions may reference later pivots; resolve recursively.
    raw = {}
    for pv, (co, rhs, lab) in pivots.items():
        raw[pv] = ((rhs, {v: -k for v, k in co.items() if v != pv and k != 0}),
                   lab)
    # Later-created pivots were reduced against all earlier ones, so their
    # expressions contain only free vars; resolve in reverse creation order.
    sol = {}
    for pv in reversed(list(raw.keys())):
        (e, lab) = raw[pv]
        acc = (e[0], dict(e[1]))
        certs = {lab: Fr(1)}
        for v in list(acc[1].keys()):
            if v in sol:
                k = acc[1].pop(v)
                (ev, ec) = sol[v]
                acc = expr_add((acc[0], acc[1]), expr_scale(ev, k))
                for l, kk in ec.items():
                    certs[l] = certs.get(l, Fr(0)) + k * kk
        acc = (acc[0], {v: k for v, k in acc[1].items() if k != 0})
        sol[pv] = (acc, certs)
    return sol, pivots

# substitute equality-derived expressions into a linear form, tracking
# certificate multipliers on the equality labels used.
def subst(coefs, bound, sol):
    """coefs: {var:Fr}; returns (expr in free vars, cert_adds {label:Fr})"""
    e = (bound, dict(coefs))
    # wait: we want sum c_v * x_v <= bound; substitute pivot vars
    newc = {}
    const = bound  # will subtract moved terms; handle via expr on LHS
    lhs = ((Fr(0), Fr(0)), {})
    certs = {}
    for v, c in coefs.items():
        if v in sol:
            (e_pv, ec) = sol[v]
            lhs = expr_add(lhs, expr_scale(e_pv, c))
            for l, kk in ec.items():
                certs[l] = certs.get(l, Fr(0)) + c * kk
        else:
            lhs = expr_add(lhs, expr_scale(expr_var(v), c))
    # lhs = (const_part, {free:coef}); constraint: lhs <= bound
    # -> {free:coef} x <= bound - const_part
    newbound = badd(bound, bneg(lhs[0]))
    return ({v: k for v, k in lhs[1].items() if k != 0}, newbound, certs)

def cert_merge(c1, c2):
    d = dict(c1)
    for l, k in c2.items():
        d[l] = d.get(l, Fr(0)) + k
    return {l: k for l, k in d.items() if k != 0}

# ---------- FM with provenance ----------
def combine(cpos, cneg, var):
    a = cpos[0][var]           # >0
    b = -cneg[0][var]          # >0
    nc = {}
    for v, k in cpos[0].items():
        if v != var: nc[v] = nc.get(v, Fr(0)) + b * k
    for v, k in cneg[0].items():
        if v != var: nc[v] = nc.get(v, Fr(0)) + a * k
    nb = badd(bscale(cpos[1], b), bscale(cneg[1], a))
    ncert = {}
    for l, k in cpos[2].items(): ncert[l] = ncert.get(l, Fr(0)) + b * k
    for l, k in cneg[2].items(): ncert[l] = ncert.get(l, Fr(0)) + a * k
    return ({v: k for v, k in nc.items() if k != 0}, nb,
            {l: k for l, k in ncert.items() if k != 0})

def fm(cons, varorder):
    cons = list(cons)
    for v in varorder:
        pos = [c for c in cons if c[0].get(v, Fr(0)) > 0]
        neg = [c for c in cons if c[0].get(v, Fr(0)) < 0]
        cons = [c for c in cons if c[0].get(v, Fr(0)) == 0]
        for cp in pos:
            for cn in neg:
                nc = combine(cp, cn, v)
                # prune: all coefs <= 0 and bound >= 0 -> trivially true
                # (vars >= 0).  Careful: only if bound c0,c1 >= 0 in the
                # relevant range; we keep it simple and drop only if both
                # coefficients nonnegative.
                if nc[0] and all(k <= 0 for k in nc[0].values()) \
                        and nc[1][0] >= 0 and nc[1][1] >= 0:
                    continue
                cons.append(nc)
    return [c for c in cons if not c[0]]

# ---------------- s=4 geometry ----------------
def fp(v, w): return (w - v) % 4
def block_gaps(v, j, k):
    lo, hi = sorted((fp(v, j), fp(v, k)))
    return list(range(lo - 1, hi - 1))

def build_system(assign, n):
    """returns (eqs, ineqs): eqs ({var:Fr}, rhs, label);
       ineqs ({var:Fr}, bound, {label:Fr})."""
    eqs, ineqs = [], []
    for v in range(4):
        C = sum(assign[v])
        eqs.append(({ (v, g): Fr(1) for g in range(3) },
                    (Fr(n - C), Fr(1)), f"V{v}"))
    for (a, b, c) in itertools.combinations(range(4), 3):
        co, C = {}, 0
        for (v, j, k) in ((a, b, c), (b, a, c), (c, a, b)):
            for gi in block_gaps(v, j, k):
                co[(v, gi)] = co.get((v, gi), Fr(0)) + 1
                C += assign[v][gi]
        eqs.append((co, (Fr(n - C), Fr(1)), f"T{a}{b}{c}"))
    def ineq(co, bound, lab):
        ineqs.append((co, bound, {lab: Fr(1)}))
    for v in range(4):
        for block in ([0], [1], [0, 1]):
            C = sum(assign[v][g] for g in block)
            ineq({(v, g): Fr(1) for g in block},
                 (Fr(n - 1 - C), Fr(1)), f"B{v}{''.join(map(str,block))}")
        for g in range(3):
            ineq({(v, g): Fr(-1)}, (Fr(0), Fr(0)), f"P{v}{g}")
            ineq({(v, g): Fr(1)}, (Fr(1), Fr(0)), f"L{v}{g}")
    return eqs, ineqs

def reduced_system(assign, n):
    """substitute equalities -> inequalities over free vars.
    Returns (cons, free) where cons = ({var:Fr}, bound (c0,c1), cert)."""
    eqs, ineqs = build_system(assign, n)
    sol, _ = gauss_solve(eqs, 12)
    cons = []
    for (co, bound, cert) in ineqs:
        nc, nb, ec = subst(co, bound, sol)
        cons.append((nc, nb, cert_merge(cert, ec)))
    free = sorted({v for c in cons for v in c[0]})
    return cons, free

def feasible(assign, n, delta):
    """vertex enumeration: free vars are original r vars -> bounded ->
    nonempty polyhedron has a vertex: choose |free| tight independent
    constraints (plus zero-var points)."""
    cons, free = reduced_system(assign, n)
    d = len(free)
    if d == 0:
        return all(bval(b, delta) >= 0 for (_, b, _) in cons)
    def ok(pt):
        for (co, b, _) in cons:
            lhs = sum(k * pt[v] for v, k in co.items())
            if lhs - (b[0] + b[1] * delta) > 0:
                return False
        return True
    # vertices from d-subsets of constraints
    import itertools as it
    idx = range(len(cons))
    for S in it.combinations(idx, d):
        # solve co_S x = b_S
        A = [[cons[i][0].get(v, Fr(0)) for v in free] for i in S]
        bb = [cons[i][1][0] + cons[i][1][1] * delta for i in S]
        pt = solve_lin(A, bb, free)
        if pt is not None and ok(pt):
            return True
    # also check origin-ish: all free = 0 (not a vertex generally, cheap)
    if ok({v: Fr(0) for v in free}):
        return True
    return False

def solve_lin(A, bb, free):
    d = len(free)
    M = [row[:] + [bb[i]] for i, row in enumerate(A)]
    for col in range(d):
        p = next((r for r in range(col, d) if M[r][col] != 0), None)
        if p is None:
            return None
        M[col], M[p] = M[p], M[col]
        for r in range(d):
            if r != col and M[r][col] != 0:
                k = M[r][col] / M[col][col]
                M[r] = [x - k * y for x, y in zip(M[r], M[col])]
    return {free[c]: M[c][d] / M[c][c] for c in range(d)}

# ---------- witness enumeration ----------
def per_vertex_profiles(s, n):
    out = []
    for ints_ in itertools.product(range(n), repeat=s - 2):
        if sum(ints_) > n - 1:
            continue
        for me in range(1, n + 1):
            tot = sum(ints_) + me
            if tot > n or tot < n - s + 2:
                continue
            k = sum(max(m - 1, 0) for m in ints_) + (me - 1)
            out.append((ints_ + (me,), k))
    return out

def witnesses_for_profile(n, ksorted):
    profs = per_vertex_profiles(4, n)
    by_k = {}
    for cells, k in profs:
        by_k.setdefault(k, []).append(cells)
    want = sorted(ksorted, reverse=True)
    opts = [by_k.get(k, []) for k in want]
    if any(not o for o in opts):
        return
    for combo in itertools.product(*opts):
        yield list(combo)

if __name__ == "__main__":
    import sys
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    dnum = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    dden = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    delta = Fr(dnum, dden)
    prof = [n - 1, n - 2, n - 2, n - 3]
    tot = infeas = 0
    survivors = []
    for w in witnesses_for_profile(n, prof):
        tot += 1
        if not feasible(w, n, delta):
            infeas += 1
        else:
            survivors.append(w)
    print(f"n={n} δ={delta} profile={prof}: {tot} witnesses, "
          f"{infeas} remainder-infeasible, {len(survivors)} survivors")
    for w in survivors[:30]:
        print("  survivor:", w)
