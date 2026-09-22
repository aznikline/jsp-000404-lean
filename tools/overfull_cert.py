#!/usr/bin/env python3
"""overfull_cert.py — corrected K3b experiment.

Fix an OVERFULL integer skeleton (Kraft sum K > cap B) and let the
exact remainder LP show *why* the primitive constraints exclude the
target regime — the certificate must produce δ >= τ by itself
(no δ < 1/2 hypothesis baked in).

For each consistent skeleton of the chosen defect profile:
  * build mode-A constraints via generic_model.build_case
  * substitute equalities (provenance-tracked)
  * run exact Fraction simplex for min δ
  * extract the Farkas combination over ORIG constraints
  * report the certificate decomposed by constraint kind:
    fan (vertex gap sums), tri (triangle sums), ang (angle <= pi-lam),
    ange/gnn (nonnegativity), rnn/rle (remainder bounds), delta

Kraft convention: defect c_i = n - k_i;  K = sum 2^{-c_i}.
Low cap B = 1 (δ < 1/2 regime), high cap B = 5/4 (δ < 1).

Usage: overfull_cert.py n s k0 k1 ... [max_leaves]
"""
import sys
from fractions import Fraction as F
from itertools import combinations

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

sys.path.insert(0, 'tools')
import generic_model as gm
import generic_enum as ge

ZERO, ONE = F(0), F(1)
CONST, DELTA = gm.CONST, gm.DELTA


def lp_min_delta_generic(ineqs):
    """Exact two-phase Fraction simplex, vars collected from ineqs.
    Adapted from remainder_check.lp_min_delta (which hardcoded s=4).
    Returns ('infeasible', None) | ('bounded', lo, y) | ('unbounded', None).
    """
    vars_ = sorted({v for q in ineqs for v in q.a
                    if v != CONST}, key=str)
    if DELTA not in vars_:
        vars_.append(DELTA)
    nv = len(vars_)
    vidx = {v: t for t, v in enumerate(vars_)}
    m = len(ineqs)
    n_art = sum(1 for q in ineqs if q.b - q.a.get(CONST, ZERO) < 0)
    ncol = nv + m + n_art + 1
    T, basis, art_cols = [], [], []
    ai = 0
    for i, q in enumerate(ineqs):
        row = [q.a.get(v, ZERO) for v in vars_]
        row += [ZERO] * m + [ZERO] * n_art
        row[nv + i] = ONE
        qb = q.b - q.a.get(CONST, ZERO)
        if qb < 0:
            row[nv + m + ai] = -ONE
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
                f_ = T[i2][c]
                T[i2] = [x - f_ * y for x, y in zip(T[i2], T[r])]
        basis[r] = c

    for i in range(m):
        if basis[i] in art_cols:
            pivot(i, basis[i])

    def drive(cost, forbidden=frozenset()):
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

    if art_cols:
        cost = [ZERO] * (ncol - 1)
        for c in art_cols:
            cost[c] = -ONE
        drive(cost)
        val = sum(T[i][-1] for i in range(m) if basis[i] in art_cols)
        if val > 0:
            return ('infeasible', None)
        for i in range(m):
            if basis[i] in art_cols:
                for j in range(nv + m):
                    if T[i][j] != 0:
                        pivot(i, j)
                        break
    cost = [ZERO] * (ncol - 1)
    cost[vidx[DELTA]] = -ONE
    ok = drive(cost, forbidden=frozenset(art_cols))
    if not ok:
        return ('unbounded', None)
    cB = [cost[b] if b < len(cost) else ZERO for b in basis]
    opt = sum(cB[i] * T[i][-1] for i in range(m))
    y = [sum(cB[i] * T[i][nv + j] for i in range(m)) for j in range(m)]
    return ('bounded', -opt, y)


def verify_cert(W):
    """Recombine ORIG forms by W; return (combo_form, ok).
    For a valid min-δ certificate the combined form must be
    δ-coefficient > 0 with all variable coefficients 0, giving
    δ >= -CONST/δcoeff after moving terms.  Also checks no negative
    weight lands on a non-equality ORIG constraint."""
    combo = gm.mk(0)
    ok = True
    for cid, w in W.items():
        if w == 0:
            continue
        con = gm.ORIG[cid]
        if not con.is_eq and w < 0:
            ok = False
        for k, c in con.form.items():
            combo[k] = combo.get(k, ZERO) + w * c
    return combo, ok


def decompose(W):
    """Group certificate weight by constraint kind."""
    by_kind = {}
    for cid, w in W.items():
        if w == 0:
            continue
        con = gm.ORIG[cid]
        by_kind.setdefault(con.kind, []).append((con.key, con.desc, w))
    return by_kind


def run(n, s, ks, max_leaves=400):
    cs = [n - k for k in ks]
    K = sum(F(1, 2) ** c for c in cs)
    print(f'n={n} s={s} ks={ks} defects c={cs} K={K} '
          f'(float {float(K):.4f})')
    VV = ge.build_VV(ks, n, s)
    print(f'variants per vertex: {[len(v) for v in VV]}')
    tris = list(combinations(range(s), 3))
    seen = 0
    best = None
    cert_shown = False
    for sol, idxs, sigkey in ge.gen_cases(ks, n, s, VV=VV,
                                        max_leaves=max_leaves):
        if not all(gm.tri_maybe(t, sol, n) for t in tris):
            continue
        gm.ORIG.clear()
        b = gm.build_case(sol, n, 'A')
        if b is None:
            continue
        ineqs, eqs = b
        sub = gm.substitute(eqs, ineqs)
        st = lp_min_delta_generic(sub)
        seen += 1
        if st[0] == 'infeasible':
            if best is None or best[0] != 'infeasible':
                best = ('infeasible',)
            continue
        if st[0] != 'bounded':
            continue
        md = st[1]
        if best is None or best[0] == 'infeasible' or md < best[1]:
            best = ('bounded', md)
            W, combo = gm.extract_cert(sub, st[2])
            if W is not None:
                cf, okc = verify_cert(W)
                dcoef = cf.get(DELTA, ZERO)
                cst = cf.get(CONST, ZERO)
                resid = {k: v for k, v in cf.items()
                         if k not in (CONST, DELTA)}
                print(f'--- new min δ = {md}  (leaf {seen}) ---')
                print(f'    combo: δcoef={dcoef} const={cst} '
                      f'residual_vars={resid} orig_ok={okc}')
                if dcoef:
                    bound = -cst / dcoef
                    print(f'    certificate proves δ ≥ {bound} '
                          f'(float {float(bound):.4f})')
                cert_shown = True
                by_kind = decompose(W)
                for kind, items in sorted(by_kind.items()):
                    print(f'    kind={kind}: {len(items)} constraints, '
                          f'weights={sorted({str(w) for _, _, w in items})}')
                    for key, desc, w in items[:12]:
                        print(f'        {w}× {desc}')
    print(f'== leaves checked: {seen}, min δ: {best}')


if __name__ == '__main__':
    n, s = int(sys.argv[1]), int(sys.argv[2])
    ks = [int(x) for x in sys.argv[3:3 + s]]
    ml = int(sys.argv[3 + s]) if len(sys.argv) > 3 + s else 400
    run(n, s, ks, ml)
