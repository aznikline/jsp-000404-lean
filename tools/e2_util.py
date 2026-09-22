"""Lane E2 (wave 2) — guided consistent-skeleton search + exact LP.

New machinery vs wave 1:

* ``float_cons`` builds the mode-A constraint set for a *partial*
  skeleton (subset of placed vertices) directly in float form —
  no Fraction substitution — so interior DFS nodes can be pruned
  by a fast LP call.

* ``guided`` is an interleaved (signature, q) DFS: at each vertex we
  pick an edge-consistent signature then a q-tuple, prune by
  tri_maybe, then by a *partial* relaxed/free LP:

    - relaxed partial-min >= 1  => subtree has no consistent leaf
      (partial constraints are a subset of the full ones, so the
      partial min is a LOWER bound for the full min).
    - in 'cex' mode additionally: partial FREE-min >= thr =>
      no leaf in the subtree can have free-min < thr, so it cannot
      be a counterexample (valid gadget bounds are <= free-min).

  Kill criteria (Lean semantics: Consistent = capped-feasible
  `0 <= d < 1`; gadget bounds <= free-min because gadget_ge is
  proved):

    T_low  dead : relaxed_min < 1 AND free_min < 1/2 AND W > 2
    T_high dead : relaxed_min < 1 AND free_min < 1   AND W > 5/2

* exact wrappers: ``mins_exact`` = (capped, relaxed, free) min-delta
  via residual_map.glp_min_delta on appropriately skipped systems.
"""
import sys, itertools, time, random
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_model as gm
import generic_enum as ge
import residual_map as rm
import seidel_lp
import lane_e_util as le

ZERO, ONE = F(0), F(1)


# ---------------------------------------------------------------------
# exact LP wrappers (Fraction simplex)
# ---------------------------------------------------------------------

def _exact(sol, n, skip):
    gm.ORIG.clear()
    b = gm.build_case(sol, n, 'A', skip=skip)
    if b is None:
        return ('buildfail', None)
    ineqs, eqs = b
    ineqs = gm.substitute(eqs, ineqs)
    st, lo, _ = rm.glp_min_delta(ineqs, gm.CONST, gm.DELTA)
    return (st, lo)


def capped_exact(sol, n):
    """min delta with 0 <= d <= 1 (the checker model)."""
    return _exact(sol, n, frozenset())


def relaxed_exact(sol, n):
    """min delta with d >= 0 only.  < 1  <=>  Lean-consistent."""
    return _exact(sol, n, {'δ<1'})


def free_exact(sol, n):
    """min delta with d completely free (Lean ModeA semantics).
    The ceiling on every valid gadget bound."""
    return _exact(sol, n, {'δ<1', 'δ≥0'})


def mins_exact(sol, n):
    """(capped_st, capped_min, relaxed_min, free_min); None-safe."""
    cst, cmin = capped_exact(sol, n)
    rst, rmin = relaxed_exact(sol, n)
    fst, fmin = free_exact(sol, n)
    return dict(capped=(cst, cmin), relaxed=(rst, rmin),
                free=(fst, fmin))


def consistent(sol, n):
    """Lean Skeleton.Consistent: exists d in [0,1) feasible."""
    st, lo = relaxed_exact(sol, n)
    return st == 'bounded' and lo < 1


# ---------------------------------------------------------------------
# float LP on a partial skeleton
# ---------------------------------------------------------------------

def float_cons(sol, placed, s, n, mode='relaxed'):
    """Constraint list for the subsystem induced by `placed` vertices.

    mode: 'relaxed' (d >= 0) | 'capped' (0 <= d <= 1) | 'free'.
    Returns (nv, cons, obj) for seidel_lp.lp_max (obj = -delta).
    """
    vidx = {}
    for v in placed:
        for g in range(s - 1):
            vidx[('r', v, g)] = len(vidx)
    di = len(vidx)
    nv = di + 1
    cons = []

    def row(expr, b):
        a = [0.0] * nv
        bb = float(b)
        for k, c in expr.items():
            if k == gm.CONST:
                bb -= float(c)
            elif k == gm.DELTA:
                a[di] += float(c)
            else:
                a[vidx[k]] += float(c)
        cons.append((a, bb))

    for v in placed:
        vv = sol[v]
        for g in range(s - 1):
            rv = ('r', v, g)
            a = [0.0] * nv
            a[vidx[rv]] = 1.0
            cons.append((a, 1.0))          # r <= 1
            a = [0.0] * nv
            a[vidx[rv]] = -1.0
            cons.append((a, 0.0))          # r >= 0
        e = gm.mk(0)
        for ge_ in vv['gaps']:
            e = gm.add(e, ge_)
        e = gm.add(e, gm.var(gm.DELTA), -ONE)
        row(e, n)
        row(gm.neg(e), -n)                 # fan equality
        oth = [x for x in range(s) if x != v]
        for u, w in itertools.combinations(oth, 2):
            a_ = vv['angles'][frozenset((u, w))]
            row(gm.add(a_, gm.var(gm.DELTA), -ONE), n - 1)
            row(gm.neg(a_), 0)
    pl = sorted(placed)
    for i, j, k in itertools.combinations(pl, 3):
        e = gm.add(sol[i]['angles'][frozenset((j, k))],
                   sol[j]['angles'][frozenset((i, k))])
        e = gm.add(e, sol[k]['angles'][frozenset((i, j))])
        e = gm.add(e, gm.var(gm.DELTA), -ONE)
        row(e, n)
        row(gm.neg(e), -n)
    if mode != 'free':
        a = [0.0] * nv
        a[di] = -1.0
        cons.append((a, 0.0))              # d >= 0
    if mode == 'capped':
        a = [0.0] * nv
        a[di] = 1.0
        cons.append((a, 1.0))              # d <= 1
    obj = [0.0] * nv
    obj[di] = -1.0
    return nv, cons, obj


def lp_min_f(nv, cons, obj):
    """Float min via scipy HiGHS (seidel_lp is exponential-slow at
    ~30 vars with equality pairs; HiGHS does these in ~ms)."""
    try:
        import numpy as np
        from scipy.optimize import linprog
        A = np.array([a for a, b in cons], dtype=float)
        B = np.array([b for a, b in cons], dtype=float)
        res = linprog(-np.asarray(obj, dtype=float), A_ub=A, b_ub=B,
                      bounds=(None, None), method='highs')
        if res.status == 2:
            return ('infeasible', None)
        if res.status == 3:
            return ('unbounded', None)
        if not res.success:
            return ('lpfail:%s' % res.message, None)
        return ('bounded', float(res.fun))
    except ImportError:
        r = seidel_lp.lp_max(nv, cons, obj, None)
        if r[0] == 'infeasible':
            return ('infeasible', None)
        if r[0] == 'unbounded':
            return ('unbounded', None)
        return ('bounded', -r[1])


def partial_min(sol, placed, s, n, mode='relaxed'):
    nv, cons, obj = float_cons(sol, placed, s, n, mode)
    return lp_min_f(nv, cons, obj)


# ---------------------------------------------------------------------
# guided (signature, q) DFS with LP pruning
# ---------------------------------------------------------------------

def q_prefilter(ktarget, n, m):
    """q-tuples surviving the one-fan range test.

    The fan forces  Sr = n + d - Sq  with 0 <= Sr <= m; relaxed
    feasibility (d >= 0) needs Sq >= n - m  (equality forces
    d = 0 exactly — the interesting boundary for the hunt), and
    Sq <= n is already enforced by q_tuples.  Vertices with
    Sq < n - m are inconsistent in EVERY skeleton — safe to drop.
    NOTE: wave-2 v1 wrongly used n-m+1, discarding the d=0-forcing
    Sq = n-s+1 variants (the strongest counterexample candidates)."""
    return [q for q in gm.q_tuples(ktarget, n, m)
            if n - m <= sum(q) <= n]


def guided(ks, n, s, mode='feas', free_thr=None, yield_partial=None,
           max_sols=5, deadline=None, node_cap=None, rng=None,
           verbose=False, qrestrict=None):
    """Interleaved signature x q DFS over vertices 0..s-1.

    mode 'feas': prune on relaxed partial-min >= 1 (keep subtrees
                 that may contain consistent skeletons).
    mode 'cex' : additionally prune on free partial-min >= free_thr
                 (keep only subtrees that may yield free_min < thr).
    mode 'free': prune on free partial-min >= free_thr only
                 (relaxed check deferred to leaf verification).

    Yields (sol_data, stats_dict) snapshots; sol_data is a deep copy.
    """
    rng = rng or random.Random()
    siglists = [le.sig_keys(v, s) for v in range(s)]
    qlists = [q_prefilter(ks[v], n, s - 1) for v in range(s)]
    if qrestrict is not None:
        qlists = [[q for q in qlists[v] if qrestrict(v, q)]
                  for v in range(s)]
    tris_by_v = [[] for _ in range(s)]
    for t in itertools.combinations(range(s), 3):
        tris_by_v[max(t)].append(t)
    sol = [None] * s
    sigs = [None] * s
    lp1 = {}                     # single-vertex relaxed feasibility
    st = dict(sig_tried=0, q_tried=0, lp_calls=0, lp1_calls=0,
              tri_rej=0, lp_rej=0, lp1_rej=0, sig_rej=0, found=0,
              nodes=0)
    t0 = time.time()
    dead = [False]

    def out_of_time():
        if dead[0]:
            return True
        if deadline and time.time() - t0 > deadline:
            dead[0] = True
        if node_cap and st['nodes'] > node_cap:
            dead[0] = True
        return dead[0]

    def rec(v):
        placed = list(range(v))
        for cand_sig in siglists[v]:
            if out_of_time():
                return
            st['sig_tried'] += 1
            ok = True
            for u in placed:
                if not le.edge_ok_sig(cand_sig, sigs[u], v, u, s):
                    ok = False
                    break
            if not ok:
                st['sig_rej'] += 1
                continue
            order, bits_t, side = cand_sig
            sigs[v] = cand_sig
            bits = dict(bits_t)
            for qs in qlists[v]:
                if out_of_time():
                    sol[v] = None
                    sigs[v] = None
                    return
                st['q_tried'] += 1
                st['nodes'] += 1
                key = (v, order, bits_t, qs)
                ok1 = lp1.get(key)
                if ok1 is None:
                    vv = le.mk_variant(v, order, bits, qs, n)
                    st['lp1_calls'] += 1
                    r = partial_min([vv if x == v else None
                                     for x in range(s)], [v], s, n,
                                    'relaxed')
                    ok1 = (r[0] == 'bounded' and r[1] < 1 - 1e-9)
                    lp1[key] = ok1
                if not ok1:
                    st['lp1_rej'] += 1
                    continue
                vv = le.mk_variant(v, order, bits, qs, n)
                sol[v] = vv
                ok = True
                for t in tris_by_v[v]:
                    if not gm.tri_maybe(t, sol, n):
                        ok = False
                        break
                if not ok:
                    st['tri_rej'] += 1
                    sol[v] = None
                    continue
                # joint LP prune
                st['lp_calls'] += 1
                r = partial_min(sol, placed + [v], s, n, 'relaxed')
                if not (r[0] == 'bounded' and r[1] < 1 - 1e-9):
                    st['lp_rej'] += 1
                    sol[v] = None
                    continue
                if mode in ('cex', 'free'):
                    st['lp_calls'] += 1
                    r = partial_min(sol, placed + [v], s, n, 'free')
                    keep = (r[0] != 'infeasible'
                            and (r[0] != 'bounded'
                                 or r[1] < free_thr - 1e-9))
                    if not keep:
                        st['lp_rej'] += 1
                        sol[v] = None
                        continue
                if v == s - 1:
                    st['found'] += 1
                    yield (le.sol_to_data(sol), dict(st))
                    if st['found'] >= max_sols:
                        dead[0] = True
                        sol[v] = None
                        sigs[v] = None
                        return
                else:
                    yield from rec(v + 1)
                sol[v] = None
            sigs[v] = None

    yield from rec(0)
    st['deadline_hit'] = dead[0] and st['found'] < max_sols
    yield (None, dict(st))


# ---------------------------------------------------------------------
# exact verification of a candidate skeleton for the kill criteria
# ---------------------------------------------------------------------

def verify_candidate(sol_data, n, s, d=None):
    """Exact (capped, relaxed, free) minima + verdict flags."""
    sol = le.data_to_sol(sol_data, n)
    mm = mins_exact(sol, n)
    if d is None:
        d = tuple(sorted(n - 1 - sum(max(q - 1, 0) for q in vv['qs'])
                         for vv in sol))
    W = le.W_of_d(tuple(sorted(d)))
    cst, cmin = mm['capped']
    rst, rmin = mm['relaxed']
    fst, fmin = mm['free']
    cons = (rst == 'bounded' and rmin < 1)
    viol = None
    if cons:
        if W > F(5, 2) and fst == 'bounded' and fmin < 1:
            viol = 'T_high'
        elif W > 2 and fst == 'bounded' and fmin < F(1, 2):
            viol = 'T_low'
    return dict(d=tuple(sorted(d)), W=W, consistent=cons,
                capped=cmin if cst == 'bounded' else str(cst),
                relaxed=rmin if rst == 'bounded' else str(rst),
                free=fmin if fst == 'bounded' else str(fst),
                viol=viol)
