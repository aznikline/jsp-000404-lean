#!/usr/bin/env python3
"""overfull_cert.py — corrected K3b experiment, strict verifier.

Fix an OVERFULL integer skeleton (Kraft sum K > cap B) and let the
exact remainder LP show *why* the primitive constraints exclude the
target regime — the certificate must produce δ >= τ by itself
(no δ < 1/2 hypothesis baked in).

Verifier contract (no LP solver involved at check time):

  Every ORIG constraint is `form = 0` (equality, any sign) or
  `form <= 0` (inequality, nonneg weight only).  A submitted
  certificate is a weight vector W over ORIG ids PLUS an explicit
  elimination: every residual variable `r` left in the recombined
  form must be canceled by a primitive bound —
    coeff > 0  ->  the `rnn` constraint `-r <= 0` at weight coeff
    coeff < 0  ->  the `rle` constraint `r <= 1` at weight -coeff
                   (which also adds `coeff` to the constant term).
  The fully eliminated form must be exactly `C - alpha*delta <= 0`
  with `alpha > 0`, and it proves `delta >= C/alpha`.  The claimed
  threshold tau is accepted iff `C >= alpha*tau` (exact Fractions).

`r <= 1` and `delta <= 1` are CLOSED relaxations of the true
strict bounds `r < 1`, `delta < 1`; they are sound for lower-bound
certificates but a boundary-feasible LP point is only
"closed-relaxation feasible", not a realizable configuration.

Usage: overfull_cert.py n s k0 k1 ... [max_leaves] [tau_num tau_den]
           [--save DIR]   dump per-leaf certificate artifacts (JSON)
"""
import json
import sys
from fractions import Fraction as F
from itertools import combinations

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

sys.path.insert(0, 'tools')
import generic_model as gm
import generic_enum as ge

ZERO, ONE = F(0), F(1)
CONST, DELTA = gm.CONST, gm.DELTA


# ---------------------------------------------------------------------
# strict certificate verifier
# ---------------------------------------------------------------------

class CertError(Exception):
    pass


def _find_bound(rvar, kind):
    """Locate the primitive bound constraint for remainder var rvar
    of the given kind ('rnn' for -r<=0, 'rle' for r<=1)."""
    vi, g = rvar[1], rvar[2]
    for cid, con in enumerate(gm.ORIG):
        if con.kind == kind and con.key == (vi, g):
            return cid
    raise CertError(f'no {kind} bound for {rvar}')


def verify_cert(W, tau):
    """Strictly verify that certificate W proves `delta >= tau`.

    Returns (alpha, C, W_full) where the fully-eliminated combined
    ORIG form is `C - alpha*delta <= 0`, and W_full extends W with
    the remainder-elimination weights.  Raises CertError otherwise.
    """
    # 1. sign legality: inequalities only get nonneg weights.
    for cid, w in W.items():
        if w == 0:
            continue
        con = gm.ORIG[cid]
        if not con.is_eq and w < 0:
            raise CertError(
                f'negative weight {w} on inequality {con.desc}')
    # 2. recombine ORIG forms.
    combo = gm.mk(0)
    for cid, w in W.items():
        if w == 0:
            continue
        for k, c in gm.ORIG[cid].form.items():
            combo[k] = combo.get(k, ZERO) + w * c
    # 3. explicit elimination of residual variables.
    W_full = dict(W)
    for v, gcoef in list(combo.items()):
        if v in (CONST, DELTA) or gcoef == 0:
            continue
        if not (isinstance(v, tuple) and v[0] == 'r'):
            raise CertError(f'unhandled variable {v} coeff {gcoef}')
        if gcoef > 0:
            cid = _find_bound(v, 'rnn')       # -r <= 0
        else:
            cid = _find_bound(v, 'rle')       #  r - 1 <= 0
        w_elim = abs(gcoef)
        W_full[cid] = W_full.get(cid, ZERO) + w_elim
        for k, c in gm.ORIG[cid].form.items():
            combo[k] = combo.get(k, ZERO) + w_elim * c
    # 4. final form must be C - alpha*delta <= 0, alpha > 0.
    resid = {k: v for k, v in combo.items()
             if k not in (CONST, DELTA) and v != 0}
    if resid:
        raise CertError(f'non-eliminated variables: {resid}')
    dcoef = combo.get(DELTA, ZERO)
    if dcoef >= 0:
        raise CertError(
            f'delta coefficient {dcoef} >= 0: cannot yield a '
            f'lower bound (d>0 gives an UPPER bound on delta)')
    alpha = -dcoef
    C = combo.get(CONST, ZERO)
    if C < alpha * tau:
        raise CertError(
            f'certificate only proves delta >= {C / alpha} < {tau}')
    return alpha, C, W_full


def decompose(W):
    by_kind = {}
    for cid, w in W.items():
        if w == 0:
            continue
        con = gm.ORIG[cid]
        by_kind.setdefault(con.kind, []).append(
            (con.key, con.desc, w))
    return by_kind


def print_cert(tag, W_full, alpha, C):
    print(f'--- {tag}: VERIFIED delta >= {C / alpha} '
          f'(float {float(C / alpha):.4f}) ---')
    print(f'    eliminated form: {C} - {alpha}*delta <= 0')
    for kind, items in sorted(decompose(W_full).items()):
        print(f'    kind={kind}: {len(items)} constraints, '
              f'weights={sorted({str(w) for _, _, w in items})}')
        for key, desc, w in items[:12]:
            print(f'        {w}x {desc}')


# ---------------------------------------------------------------------
# negative controls — every one of these MUST be rejected
# ---------------------------------------------------------------------

def selftest():
    """Build ORIG for a tiny case, then feed forged certificates."""
    n, s = 2, 3
    ks = [0] * s
    VV = ge.build_VV(ks, n, s)
    sol = next(iter(ge.gen_cases(ks, n, s, VV=VV, max_leaves=1)))[0]
    gm.ORIG.clear()
    b = gm.build_case(sol, n, 'A')
    assert b is not None
    # locate delta-hi constraint id (delta <= 1, form = d - 1).
    dhi = next(i for i, c in enumerate(gm.ORIG)
               if c.kind == 'delta' and c.key == 'hi')
    some_ineq = next(i for i, c in enumerate(gm.ORIG)
                     if not c.is_eq and c.kind != 'delta')
    cases = []

    def expect_reject(name, W, tau):
        try:
            verify_cert(W, tau)
        except CertError as e:
            cases.append((name, f'rejected: {e}'))
            return
        cases.append((name, 'NOT REJECTED — VERIFIER BUG'))

    # C1: only delta <= 1 — claims delta >= 1 but gives delta <= 1.
    expect_reject('delta<=1 alone', {dhi: ONE}, ONE)
    # C2: delta <= 1 with flipped claim — same object, tau = 1/2.
    expect_reject('flipped delta direction', {dhi: ONE}, F(1, 2))
    # C3: negative weight on an inequality.
    expect_reject('neg weight on ineq', {some_ineq: -ONE}, ZERO)
    # C4: forged residual form with insufficient constant:
    #   hand-built combo equivalent to `-delta + 0 <= 0`.
    dlo = next(i for i, c in enumerate(gm.ORIG)
               if c.kind == 'delta' and c.key == 'lo')
    # 'delta lo' is -delta <= 0: proves delta >= 0 only.
    expect_reject('insufficient constant', {dlo: ONE}, F(1, 2))
    # C5: tampered threshold — a cert that proves delta >= 0 must
    # reject tau = 1.
    expect_reject('tampered tau', {dlo: ONE}, ONE)
    # C6: residual var left that elimination cannot rescue:
    #   combine -delta<=0 with a fake leftover by giving rnn a
    #   negative... use equality-free trick: weight on 'rle' (r-1<=0)
    #   leaves +r; elimination needs rnn -r<=0 at weight 1 -> cancels
    #   but adds constant -? check it still verifies only >= -1.
    rle = next(i for i, c in enumerate(gm.ORIG) if c.kind == 'rle')
    try:
        a_, C_, _ = verify_cert({dlo: ONE, rle: ONE}, F(-2))
        cases.append(('residual via rle+rnn',
                      f'ok: proves delta >= {C_ / a_}'))
    except CertError as e:
        cases.append(('residual via rle+rnn', f'rejected: {e}'))
    for name, res in cases:
        print(f'  [{name}] {res}')
    bad = [n_ for n_, r_ in cases
           if 'NOT REJECTED' in r_]
    if bad:
        raise SystemExit(f'SELFTEST FAILED: {bad}')
    print('  selftest: all controls behaved as expected')


# ---------------------------------------------------------------------
# exact LP (unchanged) + per-leaf strict verification
# ---------------------------------------------------------------------

def lp_min_delta_generic(ineqs):
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


def dump_leaf(path, sol, n, s, W, W_full, alpha, C, tau, md):
    """Persist the full evidence record for one verified leaf."""
    rec = {
        'n': n, 's': s,
        'skeleton': [{'v': v['v'],
                      'order': list(v['order']),
                      'bits': {str(k): b for k, b in
                               v['bits'].items()},
                      'qs': list(v['qs'])}
                     for v in sol],
        'lp_min_delta': str(md),
        'target_tau': str(tau),
        'tau_met': C >= alpha * tau,
        'proven_bound': str(C / alpha),
        'eliminated_form': f'{C} - {alpha}*delta <= 0',
        'closed_relaxation_only': True,
        'relaxation_note': ('r<=1 and delta<=1 are closed '
                            'relaxations of strict r<1, delta<1'),
        'constraints': [{
            'orig_id': cid,
            'kind': gm.ORIG[cid].kind,
            'key': str(gm.ORIG[cid].key),
            'desc': gm.ORIG[cid].desc,
            'is_eq': gm.ORIG[cid].is_eq,
            'form': {str(k): str(c)
                     for k, c in gm.ORIG[cid].form.items()},
            'multiplier': str(W.get(cid, ZERO)),
            'elim_weight': str(W_full[cid] - W.get(cid, ZERO)),
        } for cid in sorted(W_full) if W_full[cid] != 0],
    }
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(rec, f, indent=1, ensure_ascii=False)


def run(n, s, ks, max_leaves=400, tau=F(1, 2), save_dir=None):
    cs = [n - k for k in ks]
    K = sum(F(1, 2) ** c for c in cs)
    print(f'n={n} s={s} ks={ks} defects c={cs} K={K} '
          f'(float {float(K):.4f})  target tau={tau}')
    print('NOTE: r<=1 and delta<=1 are CLOSED relaxations of r<1, '
          'delta<1 — feasibility here is closed-relaxation only.')
    VV = ge.build_VV(ks, n, s)
    print(f'variants per vertex: {[len(v) for v in VV]}')
    tris = list(combinations(range(s), 3))
    seen = infeasible = verified = 0
    min_delta = None
    shown = 0
    failures = []
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
            infeasible += 1
            continue
        if st[0] != 'bounded':
            continue
        md = st[1]
        if min_delta is None or md < min_delta:
            min_delta = md
        W, combo = gm.extract_cert(sub, st[2])
        if W is None:
            failures.append((seen, 'extract_cert sign failure'))
            continue
        try:
            # verify the cert proves at least the LP-reported bound
            alpha, C, W_full = verify_cert(W, md)
        except CertError as e:
            failures.append((seen, f'verify: {e}'))
            continue
        proven = C / alpha
        assert proven >= md
        hits_tau = proven >= tau
        verified += 1
        if save_dir is not None:
            import os
            os.makedirs(save_dir, exist_ok=True)
            dump_leaf(f'{save_dir}/leaf_{seen:04d}.json',
                      sol, n, s, W, W_full, alpha, C, tau, md)
        if shown < 8:
            kinds = {gm.ORIG[c].kind for c in W_full}
            if shown == 0 or 'fan' in kinds or 'rnn' in kinds:
                print_cert(f'leaf {seen} (LP min delta={md}, '
                           f'tau={tau} met: {hits_tau})',
                           W_full, alpha, C)
                shown += 1
        if not hits_tau:
            failures.append((seen,
                             f'proven bound {proven} < tau {tau}'))
    print(f'== leaves checked: {seen}, infeasible: {infeasible}, '
          f'certs strictly verified: {verified}, '
          f'failures: {len(failures)}')
    for leaf, msg in failures[:10]:
        print(f'    leaf {leaf}: {msg}')
    print(f'== closed-relaxation min delta over bounded leaves: '
          f'{min_delta}')


if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        selftest()
        sys.exit(0)
    argv = [a for a in sys.argv[1:] if not a.startswith('--')]
    save_dir = None
    for i, a in enumerate(sys.argv):
        if a == '--save' and i + 1 < len(sys.argv):
            save_dir = sys.argv[i + 1]
    n, s = int(argv[0]), int(argv[1])
    ks = [int(x) for x in argv[2:2 + s]]
    ml = int(argv[2 + s]) if len(argv) > 2 + s else 400
    tn, td = (int(argv[3 + s]), int(argv[4 + s])) \
        if len(argv) > 4 + s else (1, 2)
    run(n, s, ks, ml, F(tn, td), save_dir)
