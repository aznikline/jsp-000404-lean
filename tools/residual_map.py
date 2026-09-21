"""Map every debt certificate / MUS core to the Lean normal form.

The Lean theorem `debt_residual_ge_half` (Jsp000404/DebtChain.lean)
covers exactly certificates whose telescoped equality-residual is

    P - U - c*delta = C

where P is the positively-signed leftover (charged lower-bound debt
+ free nonnegative remainders), U the negatively-signed caps, and
    K <= P        (K = charged lower-bound total)
    U <= B + u*delta
    0 < c + u
    (c+u)/2 <= K - B - C.

This tool rebuilds a restricted system for each MUS core, extracts
the exact Farkas certificate, and checks the decomposition:
  - every lower-bound inequality's lhs must sit termwise inside P;
  - every cap inequality's lhs must sit termwise inside U;
  - leftover P coords are free nonnegative remainders;
  - leftover U coords are trivially <= 0 (r >= 0);
  - the capacity inequality holds.

Verdicts: 'mapped' | 'unmapped:<reason>'.

Usage:
  python3 residual_map.py s4            # s=4 MUS corpus json
  python3 residual_map.py s5 [NFILES]   # s=5 boundary skeletons
"""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F

FIXED = frozenset({'δ≥0', 'δ<1'})

# ---------------------------------------------------------------------
# engine adapters
# ---------------------------------------------------------------------

def load_s4():
    import remainder_check as rc
    class E:
        DELTA = rc.DELTA; CONST = rc.CONST
        ORIG = rc.ORIG
        @staticmethod
        def orig(i):
            d, f, e = rc.ORIG[i]
            return d, f, e
        build_case = staticmethod(rc.build_case)
        substitute = staticmethod(rc.substitute)
    return E

def load_g():
    import generic_model as gm
    class E:
        DELTA = gm.DELTA; CONST = gm.CONST
        ORIG = gm.ORIG
        @staticmethod
        def orig(i):
            c = gm.ORIG[i]
            return c.desc, c.form, c.is_eq
        build_case = staticmethod(gm.build_case)
        substitute = staticmethod(gm.substitute)
    return E

# ---------------------------------------------------------------------
# exact LP (remainder_check.lp_min_delta generalized to any var set)
# ---------------------------------------------------------------------

def glp_min_delta(ineqs, CONST, DELTA):
    ZERO, ONE = F(0), F(1)
    vars_ = sorted({v for q in ineqs for v in q.a
                    if v is not CONST}, key=str)
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
        row += [ZERO] * (m + n_art)
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
                rc_ = cost[j]
                for i2 in range(m):
                    if cB[i2]:
                        rc_ -= cB[i2] * T[i2][j]
                if rc_ > 0:
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
            return ('infeasible', None, None)
        for i in range(m):
            if basis[i] in art_cols:
                for j in range(nv + m):
                    if T[i][j] != 0:
                        pivot(i, j)
                        break
    cost = [ZERO] * (ncol - 1)
    cost[vidx[DELTA]] = -ONE
    if not drive(cost, forbidden=frozenset(art_cols)):
        return ('unbounded', None, None)
    cB = [cost[b] if b < len(cost) else ZERO for b in basis]
    opt = sum(cB[i] * T[i][-1] for i in range(m))
    y = [sum(cB[i] * T[i][nv + j] for i in range(m)) for j in range(m)]
    return ('bounded', -opt, y)

def extract_cert(E, ineqs_sub, y):
    W = {}
    for j, w in enumerate(y):
        if w == 0:
            continue
        for cid, c in ineqs_sub[j].p.items():
            W[cid] = W.get(cid, F(0)) + w * c
    return W

# ---------------------------------------------------------------------
# residual analysis
# ---------------------------------------------------------------------

def analyze(E, W, DELTA, CONST):
    """Decompose the certificate into residual parameters.

    Returns dict with verdict + parameters (c,u,B,K,C) or failure
    reason."""
    ZERO = F(0)
    eq_res = {}   # residual from equalities only
    ineq_use = []  # (cid, w, form, desc)
    for cid, w in W.items():
        desc, form, is_eq = E.orig(cid)
        if is_eq:
            for k, v in form.items():
                eq_res[k] = eq_res.get(k, ZERO) + w * v
        else:
            if w < 0:
                return {'verdict': 'unmapped:neg-ineq-weight',
                        'desc': desc}
            ineq_use.append((cid, w, form, desc))

    P = {k: v for k, v in eq_res.items()
         if k is not DELTA and k is not CONST and v > 0}
    U = {k: -v for k, v in eq_res.items()
         if k is not DELTA and k is not CONST and v < 0}
    c = -eq_res.get(DELTA, ZERO)
    C = -eq_res.get(CONST, ZERO)

    K, B, u = ZERO, ZERO, ZERO
    lcov = {k: ZERO for k in P}     # lower-bound coverage of P
    ucov = {k: ZERO for k in U}     # cap coverage of U
    charged, capped, other = [], [], []
    for cid, w, form, desc in ineq_use:
        a_d = form.get(DELTA, ZERO)
        c0 = form.get(CONST, ZERO)
        rpart = {k: v for k, v in form.items()
                 if k is not DELTA and k is not CONST}
        if rpart and all(v <= 0 for v in rpart.values()) \
                and a_d == 0:
            # lower bound  -rpart >= c0.  Must be a sub-expression
            # of P termwise (it charges exactly P's coordinates).
            expr_L = {k: -v for k, v in rpart.items()}
            for k, v in expr_L.items():
                if k not in lcov:
                    return {'verdict': 'unmapped:lower-not-in-P',
                            'desc': desc,
                            'need': {str(k): str(v) for k, v in
                                     expr_L.items()}}
                lcov[k] += w * v
            K += w * c0
            charged.append((desc, str(w), str(c0)))
        elif (not rpart or all(v >= 0 for v in rpart.values())) \
                and a_d <= 0:
            # cap  rpart <= -c0 + (-a_d)*delta.  Coordinates outside
            # U are extra nonnegative slack — they only relax the
            # bound on the matched part, so coverage accumulates.
            if not rpart:
                other.append((desc, str(w)))
                continue
            for k, v in rpart.items():
                if k in ucov:
                    ucov[k] += w * v
            B += w * (-c0)
            u += w * (-a_d)
            capped.append((desc, str(w)))
        else:
            return {'verdict': 'unmapped:mixed-ineq',
                    'desc': desc,
                    'form': {str(k): str(v) for k, v in
                             form.items() if v}}

    for k, v in lcov.items():
        if v > P[k]:
            return {'verdict': 'unmapped:lower-over-P',
                    'coord': str(k)}
    for k, v in U.items():
        if ucov.get(k, ZERO) < v:
            return {'verdict': 'unmapped:U-uncovered',
                    'coord': str(k), 'cov': str(ucov.get(k, ZERO))}
    P_free = {str(k): str(P[k] - lcov[k])
              for k in P if P[k] - lcov[k] > 0}
    U_free = {}
    # leftover U terms are automatically <= 0 (each r >= 0); only
    # the capped part needed a real bound.
    ok_cap = (c + u) / 2 <= K - B - C
    ok_pos = c + u > 0
    return {'verdict': 'mapped' if (ok_cap and ok_pos)
            else 'unmapped:capacity',
            'c': str(c), 'u': str(u), 'B': str(B),
            'K': str(K), 'C': str(C),
            'capacity_slack': str(K - B - C - (c + u) / 2),
            'P_free': P_free, 'U_trivial': U_free,
            'charged': charged, 'capped': capped,
            'delta_bounds_used': other}

# ---------------------------------------------------------------------
# drivers
# ---------------------------------------------------------------------

def core_restricted_cert(E, sol, n, core):
    """Build the system restricted to `core` (+FIXED), extract cert."""
    E.ORIG.clear()
    b = E.build_case(sol, n, 'A')
    if b is None:
        return None
    full = {E.orig(i)[0] for i in range(len(E.ORIG))}
    skip = (full - set(core)) - FIXED
    E.ORIG.clear()
    b = E.build_case(sol, n, 'A', skip=skip)
    ineqs, eqs = b
    ineqs = E.substitute(eqs, ineqs)
    st, lo, y = glp_min_delta(ineqs, E.CONST, E.DELTA)
    if st != 'bounded' or y is None:
        return (st, None)
    W = extract_cert(E, ineqs, y)
    return (lo, W)

def run_s4():
    import skeleton_enum as sen
    E = load_s4()
    n = 4
    data = json.load(open('mus_clusters_ks3221_0.5.json'))
    ks = (3, 2, 2, 1)
    VV = sen.build_VV(ks, n)
    stats = {}
    for cl in data:
        rep = cl['reps'][0]
        sol = [VV[v][rep['idxs'][v]] for v in range(4)]
        core = rep['descs']
        out = core_restricted_cert(E, sol, n, core)
        if out is None or out[1] is None:
            res = {'verdict': f'unmapped:lp-{out and out[0]}'}
        else:
            res = analyze(E, out[1], E.DELTA, E.CONST)
        res['min_delta'] = str(out[0]) if out else None
        res['cluster'] = cl['rank']
        stats[res['verdict']] = stats.get(res['verdict'], 0) + 1
        print(f"cluster {cl['rank']:3d} count={cl['count']:3d} "
              f"-> {res['verdict']}  c={res.get('c')} u={res.get('u')}"
              f" B={res.get('B')} K={res.get('K')} C={res.get('C')}"
              f" slack={res.get('capacity_slack')}", flush=True)
    print('\nsummary:', stats)

def run_s5(nfiles=None):
    import generic_enum as ge
    import generic_cegis as gce
    E = load_g()
    import glob, os
    files = sorted(glob.glob('gc_*_n5s5.json'))
    if nfiles:
        files = files[:nfiles]
    n, s = 5, 5
    stats = {}
    detail = []
    for fn in files:
        rep = json.load(open(fn))
        ks = rep['ks']
        VV = ge.build_VV(ks, n, s)
        for bi, idxs in enumerate(rep['boundary'][:4]):
            sol = [VV[v][idxs[v]] for v in range(s)]
            # MUS via deletion on generic engine
            E.ORIG.clear()
            E.build_case(sol, n, 'A')
            full = {E.orig(i)[0] for i in range(len(E.ORIG))}
            alive = full - FIXED
            for d in sorted(alive):
                skip = ((full - alive) | {d}) - FIXED
                E.ORIG.clear()
                b = E.build_case(sol, n, 'A', skip=skip)
                if b is None:
                    alive.discard(d)
                    continue
                inq, eq = b
                inq = E.substitute(eq, inq)
                st = gce.lp_min_delta_f(inq)
                if st[0] == 'infeasible' or (
                        st[0] == 'bounded' and st[1] >= 0.5 - 1e-9):
                    alive.discard(d)
            out = core_restricted_cert(E, sol, n, alive | FIXED)
            if out is None or out[1] is None:
                res = {'verdict': f'unmapped:lp-{out and out[0]}'}
            else:
                res = analyze(E, out[1], E.DELTA, E.CONST)
            tag = f"{fn}:{bi} size={len(alive)}"
            stats[res['verdict']] = stats.get(res['verdict'], 0) + 1
            detail.append({'file': fn, 'idxs': idxs,
                           'mus': sorted(alive), **res})
            print(f"{tag} -> {res['verdict']}  c={res.get('c')} "
                  f"u={res.get('u')} B={res.get('B')} K={res.get('K')}"
                  f" C={res.get('C')} slack={res.get('capacity_slack')}",
                  flush=True)
    print('\nsummary:', stats)
    with open('residual_map_s5.json', 'w') as f:
        json.dump(detail, f, indent=1)
    print('-> residual_map_s5.json')

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 's4':
        run_s4()
    elif len(sys.argv) > 1 and sys.argv[1] == 's5':
        run_s5(int(sys.argv[2]) if len(sys.argv) > 2 else None)
    else:
        print('usage: residual_map.py s4 | s5 [nfiles]')
