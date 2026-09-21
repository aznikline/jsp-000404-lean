#!/usr/bin/env python3
"""
remainder_check.py — exact remainder/carry feasibility checker for the
JSP-000404 (Sendov minimax angle, Erdős #504) staircase crux.

Question: can an exponent profile be realized at s = 4 centers for a
given δ?  Pure integer-cell counting cannot see δ, so the obstruction
must live in the fractional remainders

    gap / λ = q + r,   0 ≤ r < 1,   λ = 2π/u,  u = 2n + 2δ,  π/λ = n + δ.

For every combinatorial skeleton (per-vertex fan order × lift pattern)
and every integer cell assignment achieving the profile we build the
exact linear system over the remainders r and a symbolic δ:

  * per-vertex exact sum      Σ gaps = n + δ              (Σ gaps = π)
  * triangle angle sums       A_i + A_j + A_k = n + δ     (per triangle)
  * triangle angles ≤ π − λ   angle ≤ n − 1 + δ           (modA, provable)
  * facing-gap (4.12)         g_i^σ + g_j^σ ≥ 1           (per edge side)
  * 0 ≤ r ≤ 1                 (r < 1 approximated by ≤ 1)

then eliminate all r variables (equalities by substitution, the rest by
Fourier–Motzkin) leaving constraints on δ alone, with a Farkas
provenance vector on every derived inequality.

  --mode A : provable contract only (angle upper bound + facing lower)
  --mode B : add angle ≥ λ (two-sided window; NOT provable from GA)
"""

from fractions import Fraction as F
from itertools import permutations, combinations, product
import sys, time

ZERO, ONE = F(0), F(1)
DELTA = 'δ'
CONST = 'c'
N = 4                      # n: π/λ = n + δ

# ---------------------------------------------------------------------
# affine expressions: dict {var: coeff}; CONST holds the constant term
# ---------------------------------------------------------------------

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

# ---------------------------------------------------------------------
# per-vertex skeleton variants
# ---------------------------------------------------------------------

def q_tuples(ktarget, n):
    out = set()
    for qs in product(range(n + 1), repeat=3):
        if sum(max(q - 1, 0) for q in qs) == ktarget and sum(qs) <= n:
            out.add(qs)
    return sorted(out)

def vertex_variants(vi, ktarget, others, n):
    """Local skeletons at vertex vi achieving exponent ktarget.

    Variant = (order, bits, qs):
      order (d1,d2,d3): cyclic fan order; gaps a:(d1→d2) b:(d2→d3) c:(d3→d1)
      bits  {v: 0/1}:   2π lift pattern, d1 fixed to 0 (global flip)
      qs    (qa,qb,qc): integer cells of the three gaps.
    """
    out = []
    for order in permutations(others):
        d1, d2, d3 = order
        pos = {d1: 0, d2: 1, d3: 2}
        for b2, b3 in product((0, 1), repeat=2):
            bits = {d1: 0, d2: b2, d3: b3}
            for qs in q_tuples(ktarget, n):
                ra, rb, rc = ('r', vi, 0), ('r', vi, 1), ('r', vi, 2)
                ea = add(mk(qs[0]), var(ra))
                eb = add(mk(qs[1]), var(rb))
                ec = add(mk(qs[2]), var(rc))
                arcs = {frozenset((d1, d2)): ea,
                        frozenset((d2, d3)): eb,
                        frozenset((d1, d3)): add(ea, eb)}
                angles = {}
                for u, v in combinations(others, 2):
                    arc = arcs[frozenset((u, v))]
                    if bits[u] == bits[v]:
                        angles[frozenset((u, v))] = arc
                    else:
                        angles[frozenset((u, v))] = \
                            add(add(mk(n), var(DELTA)), arc, -ONE)
                side = {}
                for j in others:
                    for k in others:
                        if k == j:
                            continue
                        if bits[k] == bits[j]:
                            side[(j, k)] = 1 if pos[k] > pos[j] else -1
                        else:
                            side[(j, k)] = 1 if pos[k] < pos[j] else -1
                out.append(dict(v=vi, order=order, bits=bits, qs=qs,
                                gaps=[ea, eb, ec], arcs=arcs,
                                angles=angles, side=side))
    return out

# ---------------------------------------------------------------------
# constraints
# ---------------------------------------------------------------------

class C:
    """inequality  a·x ≤ b  with provenance {orig_id: coeff}"""
    __slots__ = ('a', 'b', 'p')
    def __init__(self, a, b, p):
        self.a = {k: v for k, v in a.items() if v != 0 or k == CONST}
        self.b = F(b)
        self.p = {k: v for k, v in p.items() if v != 0}

ORIG = []
def oreg(desc, form, is_eq):
    ORIG.append((desc, form, is_eq))
    return len(ORIG) - 1

def build_case(vs, n, mode, skip=frozenset()):
    ineqs, eqs = [], []
    def I(desc, expr, b):
        if desc in skip:
            return
        cid = oreg(desc, add(expr, mk(-b)), False)
        ineqs.append(C(expr, b, {cid: ONE}))
    def E(desc, expr, rhs):
        if desc in skip:
            return
        cid = oreg(desc, add(expr, mk(-rhs)), True)
        eqs.append([expr, F(rhs), {cid: ONE}])

    for vi in range(4):
        for g in range(3):
            rv = ('r', vi, g)
            I(f'r{vi}{g}≥0', neg(var(rv)), ZERO)
            I(f'r{vi}{g}≤1', var(rv), ONE)
    I('δ≥0', neg(var(DELTA)), ZERO)
    I('δ<1', var(DELTA), ONE)                    # δ < 1 as ≤ 1
    for vi in range(4):
        e = add(add(vs[vi]['gaps'][0], vs[vi]['gaps'][1]),
                vs[vi]['gaps'][2])
        e = add(e, var(DELTA), -ONE)             # Σgaps − δ = n
        E(f'V{vi} Σgap=π', e, n)
    for tri in combinations(range(4), 3):
        i, j, k = tri
        e = add(vs[i]['angles'][frozenset((j, k))],
                vs[j]['angles'][frozenset((i, k))])
        e = add(e, vs[k]['angles'][frozenset((i, j))])
        e = add(e, var(DELTA), -ONE)             # A+B+C − δ = n
        E(f'Δ{tri} Σ=π', e, n)
    for i in range(4):
        oth = [x for x in range(4) if x != i]
        for u, v in combinations(oth, 2):
            a = vs[i]['angles'][frozenset((u, v))]
            I(f'∠{i}{u}{v}≤π−λ', add(a, var(DELTA), -ONE), n - 1)
            if mode == 'B':
                I(f'∠{i}{u}{v}≥λ', neg(a), -ONE)
            else:
                I(f'∠{i}{u}{v}≥0', neg(a), ZERO)
    for vi in range(4):
        for gi, ge in enumerate(vs[vi]['gaps']):
            I(f'g{vi}{gi}≥0', neg(ge), ZERO)
    if mode == 'B':
        # Full (4.12): for each edge+side, the facing gaps θ,ψ
        # (projective distance from the edge-direction to the nearest
        # same-side direction, i.e. min over k of min(arc, π−arc))
        # satisfy  λ ≤ θ + ψ ≤ π − λ.   Since min over pairs of
        # a+b equals minA + minB, requiring all pairs is EXACT.
        # NOTE: not provable from GA alone — model-B experiment only.
        for i, j in combinations(range(4), 2):
            for σ in (1, -1):
                ki_ = sorted(k for k in range(4) if k != i and k != j
                             and vs[i]['side'][(j, k)] == σ)
                kj_ = sorted(k for k in range(4) if k != i and k != j
                             and vs[j]['side'][(i, k)] == -σ)
                if ki_ != kj_:
                    return None
                if not ki_:
                    continue
                ci, cj = [], []
                for k in ki_:
                    arc = vs[i]['arcs'][frozenset((j, k))]
                    ci += [arc,
                           add(add(mk(n), var(DELTA)), arc, -ONE)]
                for k in kj_:
                    arc = vs[j]['arcs'][frozenset((i, k))]
                    cj += [arc,
                           add(add(mk(n), var(DELTA)), arc, -ONE)]
                for a in ci:
                    for b in cj:
                        ab = add(a, b)
                        # λ ≤ θ+ψ :  −(a+b) ≤ −1
                        I(f'f{i}{j}σ{σ:+d}lo', neg(ab), -ONE)
    return ineqs, eqs

# ---------------------------------------------------------------------
# elimination
# ---------------------------------------------------------------------

def substitute(eqs, ineqs):
    """Eliminate one r-var per equality; substitute everywhere."""
    eqs = [[dict(e), r, dict(p)] for e, r, p in eqs]
    while True:
        idx = None
        for t, (e, rhs, p) in enumerate(eqs):
            if any(v not in (CONST, DELTA) and c != 0 for v, c in e.items()):
                idx = t
                break
        if idx is None:
            break
        e, rhs, p = eqs.pop(idx)
        piv = next(v for v, c in e.items()
                   if v not in (CONST, DELTA) and c != 0)
        cp = e[piv]
        rest = dict(e); rest.pop(piv)
        expr = {k: -c / cp for k, c in rest.items()}
        expr[CONST] = expr.get(CONST, ZERO) + rhs / cp
        provE = {k: c / cp for k, c in p.items()}   # piv−expr = (1/cp)(e−rhs)
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
                pv2[k] = pv2.get(k, ZERO) - c * cc   # −c·(piv−expr)
            return A, pv2
        for iq in ineqs:
            iq.a, iq.p = subst(iq.a, iq.p)
        for t in eqs:
            t[0], t[2] = subst(t[0], t[2])
    for e, rhs, p in eqs:          # leftover δ/const equalities → two ineqs
        ineqs.append(C(e, rhs, p))
        ineqs.append(C(neg(e), -rhs, {k: -c for k, c in p.items()}))
    return ineqs

def fm(ineqs, v):
    pos = [q for q in ineqs if q.a.get(v, ZERO) > 0]
    ngt = [q for q in ineqs if q.a.get(v, ZERO) < 0]
    out = [q for q in ineqs if v not in q.a]
    seen = {(tuple(sorted(q.a.items(), key=lambda kv: str(kv[0]))), q.b)
            for q in out}
    for P in pos:
        cp = P.a[v]
        for Ng in ngt:
            cn = -Ng.a[v]
            a = {}
            for k, val in P.a.items():
                a[k] = a.get(k, ZERO) + cn * val
            for k, val in Ng.a.items():
                a[k] = a.get(k, ZERO) + cp * val
            a.pop(v, None)
            b = cn * P.b + cp * Ng.b
            pr = {}
            for k, val in P.p.items():
                pr[k] = pr.get(k, ZERO) + cn * val
            for k, val in Ng.p.items():
                pr[k] = pr.get(k, ZERO) + cp * val
            key = (tuple(sorted(a.items(), key=lambda kv: str(kv[0]))), b)
            if key in seen:
                continue
            seen.add(key)
            out.append(C(a, b, pr))
    return out

# ---------------------------------------------------------------------
# exact two-phase simplex over Fraction:  maximize obj·x  s.t. a·x ≤ b, x ≥ 0
# ---------------------------------------------------------------------

def lp_min_delta(ineqs):
    """Minimize δ s.t. constraints.  Exact two-phase simplex.

    All decision vars are the r-vars (≥0 enforced by explicit ineqs) and
    δ (≥0 enforced).  Returns
      ('infeasible', cert) | ('bounded', lo, cert_binding)
    where cert gives a nonneg combination of original constraints
    proving the bound, when extractable.
    """
    vars_ = [('r', vi, g) for vi in range(4) for g in range(3)]
    vars_.append(DELTA)
    # Canonical row form for EVERY constraint:  a·x + s_i = b  (s_i ≥ 0).
    # b_i ≥ 0 → slack basic.  b_i < 0 → add artificial  a·x + s_i − t_i = b
    # with t_i basic (t_i = −b > 0 at origin).  With t_i = 0 both recover
    # exactly a·x ≤ b, so dual weights are Farkas weights on the ORIGINAL
    # constraints directly.
    m = len(ineqs)
    nv = len(vars_)
    vidx = {v: t for t, v in enumerate(vars_)}
    n_art = sum(1 for q in ineqs
                if q.b - q.a.get(CONST, ZERO) < 0)
    ncol = nv + m + n_art + 1
    T = []
    basis = []
    art_cols = []
    ai = 0
    for i, q in enumerate(ineqs):
        row = [q.a.get(v, ZERO) for v in vars_]
        row += [ZERO] * m
        row += [ZERO] * n_art
        row[nv + i] = ONE                   # slack +1
        qb = q.b - q.a.get(CONST, ZERO)     # CONST lives inside q.a
        if qb < 0:
            row[nv + m + ai] = -ONE         # artificial −1
            basis.append(nv + m + ai)
            art_cols.append(nv + m + ai)
            ai += 1
        else:
            basis.append(nv + i)
        row.append(qb)
        T.append(row)

    def pivot(r, c):
        pv = T[r][c]
        T[r] = [x / pv for x in T[r]]
        for i2 in range(m):
            if i2 != r and T[i2][c] != 0:
                f = T[i2][c]
                T[i2] = [x - f * y for x, y in zip(T[i2], T[r])]
        basis[r] = c

    # normalize artificial basis columns to coefficient +1
    for i in range(m):
        if basis[i] in art_cols:
            pivot(i, basis[i])

    def drive(cost, forbidden=frozenset()):
        """maximize Σ cost_j x_j ; returns True if optimal reached.
        Bland's rule (smallest index) for anti-cycling."""
        while True:
            cB = [cost[b] if b < len(cost) else ZERO for b in basis]
            bj = None
            for j in range(ncol - 1):
                if j in forbidden or j in basis:
                    continue
                rc = cost[j]
                for i2 in range(m):
                    if cB[i2]:
                        rc -= cB[i2] * T[i2][j]
                if rc > 0:
                    bj = j
                    break
            if bj is None:
                return True
            bi, brt = None, None
            for i2 in range(m):
                if T[i2][bj] > 0:
                    r_ = T[i2][-1] / T[i2][bj]
                    if brt is None or r_ < brt or \
                            (r_ == brt and basis[i2] < basis[bi]):
                        brt, bi = r_, i2
            if bi is None:
                return False
            pivot(bi, bj)

    # Phase 1: minimize Σ artificials → maximize -Σ artif
    if art_cols:
        cost = [ZERO] * (ncol - 1)
        for c in art_cols:
            cost[c] = -ONE
        drive(cost)
        val = sum(T[i][-1] for i in range(m) if basis[i] in art_cols)
        if val > 0:
            return ('infeasible', None)
        # drive artificials out of basis (degenerate pivots allowed)
        for i in range(m):
            if basis[i] in art_cols:
                for j in range(nv + m):
                    if T[i][j] != 0:
                        pivot(i, j)
                        break
    # Phase 2: maximize -δ  (artificial columns may never re-enter)
    cost = [ZERO] * (ncol - 1)
    cost[vidx[DELTA]] = -ONE
    ok = drive(cost, forbidden=frozenset(art_cols))
    if not ok:
        return ('unbounded', None)
    # optimal δ = -objective; objective value = Σ cB·rhs
    cB = [cost[b] if b < len(cost) else ZERO for b in basis]
    opt = sum(cB[i] * T[i][-1] for i in range(m))
    # duals of the original ≤-rows:  y_j = cBᵀ B⁻¹ e_j (slack columns)
    y = [sum(cB[i] * T[i][nv + j] for i in range(m)) for j in range(m)]
    return ('bounded', -opt, y)

def extract_cert(ineqs_sub, y):
    """Map dual weights on substituted ineqs back to ORIG constraints.
    Returns (W, combo) where W = {orig_cid: weight} and combo is the
    combined affine form (should be  lo − δ, i.e.  δ ≥ lo), or None if
    invalid (negative weight on a non-equality constraint)."""
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
        if not ORIG[cid][2] and w < 0:
            return None
        for k, c in ORIG[cid][1].items():
            combo[k] = combo.get(k, ZERO) + w * c
    return W, combo

def verify_form(prov):
    """Recombine ORIG forms by prov; return the resulting ≤0 form."""
    combo = mk(0)
    for cid, w in prov.items():
        _, form, _ = ORIG[cid]
        for k, c in form.items():
            combo[k] = combo.get(k, ZERO) + w * c
    return combo

# ---------------------------------------------------------------------
# cheap integer/interval precheck per triangle
# ---------------------------------------------------------------------

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
    # need  c + R + dc·δ = n + δ,  R∈[rmin,rmax], δ∈[0,1)
    lo = (n - c) + min(ZERO, ONE - dc)
    hi = (n - c) + max(ZERO, ONE - dc)
    return lo <= rmax and hi >= rmin

# ---------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------

def main():
    mode = 'B' if '--mode' in sys.argv and \
        sys.argv[sys.argv.index('--mode') + 1] == 'B' else 'A'
    max_fm = int(sys.argv[sys.argv.index('--max-fm') + 1]) \
        if '--max-fm' in sys.argv else 2000
    n = N
    t0 = time.time()
    stats = dict(cases=0, edge_pruned=0, tri_pruned=0, fm=0, feas=0,
                 infeas=0, fm_time=0.0)
    results = []
    # vertices 1,2,3 symmetric: run the k=1 representative at vertex 3.
    ks = [3, 2, 2, 1]
    VV = [vertex_variants(v, ks[v],
                          tuple(x for x in range(4) if x != v), n)
          for v in range(4)]
    print(f'VV sizes={[len(v) for v in VV]}', flush=True)
    # side signatures: sig[i][j] per variant-index = 2-bit pattern
    # (side of k1, side of k2 wrt ray i->j), k1<k2 the two remaining.
    sig = {}
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            rem = sorted(k for k in range(4) if k != i and k != j)
            sig[(i, j)] = [
                (1 if vv['side'][(j, rem[0])] == 1 else 0) |
                (2 if vv['side'][(j, rem[1])] == 1 else 0)
                for vv in VV[i]]
    def edge_ok(i, j, iv, jv):
        return sig[(i, j)][iv] == (3 - sig[(j, i)][jv])
    sol = [None] * 4
    soli = [-1] * 4
    def bt(i):
        if stats['fm'] >= max_fm:
            return
        if i == 4:
            stats['cases'] += 1
            if stats['cases'] % 2000 == 0:
                print(f'  leaves={stats["cases"]} fm={stats["fm"]} '
                      f'fm_t={stats["fm_time"]:.0f}s '
                      f'total={time.time()-t0:.0f}s', flush=True)
            for tri in combinations(range(4), 3):
                if not tri_maybe(tri, sol, n):
                    stats['tri_pruned'] += 1
                    return
            stats['fm'] += 1
            ORIG.clear()
            built = build_case(sol, n, mode)
            if built is None:
                stats['edge_pruned'] += 1
                return
            ineqs, eqs = built
            tfm = time.time()
            ineqs = substitute(eqs, ineqs)
            res = lp_min_delta(ineqs)
            stats['fm_time'] += time.time() - tfm
            results.append((res, ineqs))
            if res[0] == 'infeasible':
                stats['infeas'] += 1
            else:
                stats['feas'] += 1
            return
        for idx, vv in enumerate(VV[i]):
            if all(edge_ok(i, j, idx, soli[j]) for j in range(i)):
                sol[i] = vv
                soli[i] = idx
                bt(i + 1)
                sol[i] = None
                soli[i] = -1
            else:
                stats['edge_pruned'] += 1
    bt(0)
    print(f'mode={mode} leaf_cases={stats["cases"]} fm={stats["fm"]} '
          f'feasible={stats["feas"]} infeasible={stats["infeas"]} '
          f'edge_pruned={stats["edge_pruned"]} tri_pruned={stats["tri_pruned"]} '
          f'time={time.time()-t0:.1f}s')
    feas = [(res, ineqs) for res, ineqs in results
            if res[0] == 'bounded']
    unb = [res for res, _ in results if res[0] == 'unbounded']
    if unb:
        print(f'WARNING: {len(unb)} unbounded cases (δ unconstrained)')
    if not feas:
        print('ALL surviving cases infeasible — profile killed '
              '(subject to boundary r<1).')
        return
    los = [res[1] for res, _ in feas]
    gmin = min(los)
    print(f'feasible cases={len(feas)}; min δ over cases = {gmin}; '
          f'max of per-case minima = {max(los)}')
    print('δ lower-bound histogram:',
          sorted({str(l): los.count(l) for l in set(los)}.items()))
    # show certificate for a case attaining the global minimum
    for res, ineqs in feas:
        if res[1] == gmin:
            out = extract_cert(ineqs, res[2])
            if out is None:
                print(f'δ ≥ {gmin}: certificate extraction FAILED '
                      '(negative weight on inequality)')
            else:
                W, combo = out
                print(f'example certificate for δ ≥ {gmin}:')
                for cid, w in sorted(W.items()):
                    if w != 0:
                        print(f'   {w} × [{ORIG[cid][0]}]')
                print('   combined form:', combo)
            break

if __name__ == '__main__':
    main()
