"""Lane V1 — vacuum-lemma falsification hunt in the LEAN model.

Lean semantics (Jsp000404.Gadget.ModeA + Skeleton.Proper):
  * pos injective on others (permutation)          -> kept
  * bits arbitrary (mod global flip)               -> kept
  * q : Z^m  (NO 0<=q<=n, NO per-gap q+r>=0!)      -> extended
  * NO edge-side consistency                       -> dropped
  * Consistent = relaxed LP min < 1 (0<=r<=1, fan, tri, ang bounds,
    d>=0 free of cap)

We search W > 5/2 profiles at s=4 for any consistent skeleton.
If one exists, `Proper -> Consistent -> W <= 5/2` is FALSE.
"""
import sys, itertools, time, random
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_model as gm
import lane_e_util as le
import e2_util


def q_tuples_ext(ktarget, n, m):
    """Lean-faithful q's: cells can be negative.

    Bounds justified by the arc structure (proper skeleton):
      * gaps 0..m-2 appear in singleton arcs (consecutive positions)
        -> q_g + r_g >= 0 (direct) or >= 1 (comp) forces q_g >= -1.
      * gap m-1 (wrap) is in no arc; fan bounds it via
        n - m <= sum(q) <= n (needs Sr = n-sum+d in [0,m], d<1).
    """
    lo, hi = -1, n
    out = []
    # last cell bounded below by fan: q_last >= n - m - (m-1)*hi
    llast = n - m - (m - 1) * hi
    for qs in itertools.product(range(lo, hi + 1), repeat=m - 1):
        for ql in range(llast, hi + 3):
            full = qs + (ql,)
            if sum(max(q - 1, 0) for q in full) != ktarget:
                continue
            s = sum(full)
            if n - m <= s <= n:
                out.append(full)
    return out


def guided_lean(ks, n, s, max_sols=5, deadline=None, node_cap=None,
                rng=None, verbose=True, qrestrict=None,
                fix_first_order=True):
    """DFS like e2_util.guided but WITHOUT edge-side consistency and
    with extended q lists (Lean model)."""
    rng = rng or random.Random()
    siglists = [le.sig_keys(v, s) for v in range(s)]
    qlists = [q_tuples_ext(ks[v], n, s - 1) for v in range(s)]
    if qrestrict is not None:
        qlists = [[q for q in qlists[v] if qrestrict(v, q)]
                  for v in range(s)]
    if fix_first_order and s > 0:
        # WLOG vertex 0's order is the identity permutation
        siglists[0] = [sig for sig in siglists[0]
                       if sig[0] == tuple(range(1, s))]
    tris_by_v = [[] for _ in range(s)]
    for t in itertools.combinations(range(s), 3):
        tris_by_v[max(t)].append(t)
    sol = [None] * s
    lp1 = {}
    st = dict(sig_tried=0, q_tried=0, lp_calls=0, lp1_calls=0,
              tri_rej=0, lp_rej=0, lp1_rej=0, found=0, nodes=0)
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
            order, bits_t, side = cand_sig
            bits = dict(bits_t)
            for qs in qlists[v]:
                if out_of_time():
                    sol[v] = None
                    return
                st['q_tried'] += 1
                st['nodes'] += 1
                key = (v, order, bits_t, qs)
                ok1 = lp1.get(key)
                if ok1 is None:
                    vv = le.mk_variant(v, order, bits, qs, n)
                    st['lp1_calls'] += 1
                    r = e2_util.partial_min(
                        [vv if x == v else None for x in range(s)],
                        [v], s, n, 'relaxed')
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
                st['lp_calls'] += 1
                r = e2_util.partial_min(sol, placed + [v], s, n,
                                        'relaxed')
                if not (r[0] == 'bounded' and r[1] < 1 - 1e-9):
                    st['lp_rej'] += 1
                    sol[v] = None
                    continue
                if v == s - 1:
                    st['found'] += 1
                    yield (le.sol_to_data(sol), dict(st))
                    if st['found'] >= max_sols:
                        dead[0] = True
                        sol[v] = None
                        return
                else:
                    yield from rec(v + 1)
                sol[v] = None

    yield from rec(0)
    st['deadline_hit'] = dead[0] and st['found'] < max_sols
    yield (None, dict(st))


def lean_consistent_exact(sol_data, n, s):
    """Exact check of Lean consistency: relaxed LP min < 1, but with
    the gnn (per-gap >=0) constraints REMOVED (Lean ModeA lacks them).
    Also no edge-consistency needed — sol already fixed."""
    import residual_map as rm
    sol = le.data_to_sol(sol_data, n)
    gm.ORIG.clear()
    b = gm.build_case(sol, n, 'A', skip={'δ<1', 'gnn'})
    if b is None:
        return ('buildfail', None)
    ineqs, eqs = b
    ineqs = gm.substitute(eqs, ineqs)
    st, lo, _ = rm.glp_min_delta(ineqs, gm.CONST, gm.DELTA)
    return (st, lo)


if __name__ == '__main__':
    s, n = 4, 4
    ks = [int(x) for x in sys.argv[1].split(',')] \
        if len(sys.argv) > 1 else [3, 3, 2, 2]
    deadline = float(sys.argv[2]) if len(sys.argv) > 2 else 60
    max_sols = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    d = tuple(sorted(n - 1 - k for k in ks))
    W = le.W_of_d(d)
    print(f'profile k={ks} d={d} W={W} (>{F(5,2)}? {W > F(5,2)})',
          flush=True)
    found = []
    for sol_data, st in guided_lean(ks, n, s, max_sols=max_sols,
                                  deadline=deadline):
        if sol_data is None:
            print('STATS', st, flush=True)
            continue
        stx, lo = lean_consistent_exact(sol_data, n, s)
        print('LEAF relaxed-exact:', stx, lo, flush=True)
        if stx == 'bounded' and lo < 1:
            print('*** CONSISTENT (Lean) skeleton at W>5/2 ***',
                  flush=True)
            print(sol_data, flush=True)
            found.append(sol_data)
    print('done, consistent found:', len(found))
