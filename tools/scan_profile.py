"""Scan all edge-consistent skeletons for profile (3,2,2,1) at n=4.

For each skeleton: float-LP min δ.  Report distribution; keep the
skeletons with smallest min-δ for exact verification.
"""
import sys, time, itertools, importlib.util
spec = importlib.util.spec_from_file_location(
    'rc', 'tools/remainder_check.py')
rc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rc)
n = rc.N
DELTA = rc.DELTA

# ---------------------------------------------------------------------
# Seidel incremental LP (float) — see seidel_lp.py
# ---------------------------------------------------------------------

import seidel_lp

VARS5 = [('r', vi, g) for vi in range(4) for g in range(3)] + [DELTA]
V5IDX = {v: t for t, v in enumerate(VARS5)}

def lp_min_delta_f(ineqs):
    present = sorted({v for q in ineqs for v in q.a
                      if v not in (rc.CONST,)},
                     key=str)
    if DELTA not in present:
        # δ eliminated entirely: just feasibility check via any δ
        present.append(DELTA)
    idx = {v: t for t, v in enumerate(present)}
    nv = len(present)
    cons = []
    for q in ineqs:
        a = [float(q.a.get(v, 0)) for v in present]
        b = float(q.b) - float(q.a.get(rc.CONST, 0))
        cons.append((a, b))
    obj = [0.0] * nv
    obj[idx[DELTA]] = -1.0
    bounds = [(0.0, 1.0)] * nv
    r = seidel_lp.lp_max(nv, cons, obj, bounds)
    if r[0] == 'infeasible':
        return ('infeasible', None)
    if r[0] == 'unbounded':
        return ('unbounded', None)
    return ('bounded', -r[1], None)

# ---------------------------------------------------------------------
# enumeration: signatures first, then q-level DFS with tri pruning
# ---------------------------------------------------------------------

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'A'
    max_leaves = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    ks = [3, 2, 2, 1]
    VV = [rc.vertex_variants(v, ks[v],
                              tuple(x for x in range(4) if x != v), n)
          for v in range(4)]
    # group variants by signature (order,bits)
    sigvars = [dict() for _ in range(4)]
    for i in range(4):
        for idx, vv in enumerate(VV[i]):
            key = (vv['order'], tuple(sorted(vv['bits'].items())))
            sigvars[i].setdefault(key, []).append(idx)
    sig = {}
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            rem = sorted(k for k in range(4) if k != i and k != j)
            sig[(i, j)] = {}
            for key, idxs in sigvars[i].items():
                vv = VV[i][idxs[0]]
                sig[(i, j)][key] = \
                    (1 if vv['side'][(j, rem[0])] == 1 else 0) | \
                    (2 if vv['side'][(j, rem[1])] == 1 else 0)

    def edge_ok(i, j, ki, kj):
        return sig[(i, j)][ki] == (3 - sig[(j, i)][kj])

    keys = [list(s.keys()) for s in sigvars]
    t0 = time.time()
    stats = dict(sig=0, leaves=0, tri_pruned=0, infeas=0,
                 bounded=0, unb=0)
    results = []        # (minδ, sigkey4, qidx4)
    for k0 in keys[0]:
        for k1 in keys[1]:
            if not edge_ok(1, 0, k1, k0):
                continue
            for k2 in keys[2]:
                if not (edge_ok(2, 0, k2, k0)
                        and edge_ok(2, 1, k2, k1)):
                    continue
                for k3 in keys[3]:
                    if not (edge_ok(3, 0, k3, k0)
                            and edge_ok(3, 1, k3, k1)
                            and edge_ok(3, 2, k3, k2)):
                        continue
                    stats['sig'] += 1
                    # q-level DFS: v0,v1,v2 → tri(0,1,2) → v3
                    sol = [None] * 4
                    for i0 in sigvars[0][k0]:
                        sol[0] = VV[0][i0]
                        for i1 in sigvars[1][k1]:
                            sol[1] = VV[1][i1]
                            for i2 in sigvars[2][k2]:
                                sol[2] = VV[2][i2]
                                if not rc.tri_maybe(
                                        (0, 1, 2), sol, n):
                                    stats['tri_pruned'] += 1
                                    continue
                                for i3 in sigvars[3][k3]:
                                    sol[3] = VV[3][i3]
                                    stats['leaves'] += 1
                                    if stats['leaves'] % 20000 == 0:
                                        print(f'  {stats["leaves"]} leaves, '
                                              f'{stats["bounded"]} bounded, '
                                              f'{time.time()-t0:.0f}s',
                                              flush=True)
                                    if stats['leaves'] > max_leaves:
                                        break
                                    if not all(
                                            rc.tri_maybe(t, sol, n)
                                            for t in
                                            ((0, 1, 3), (0, 2, 3),
                                             (1, 2, 3))):
                                        stats['tri_pruned'] += 1
                                        continue
                                    rc.ORIG.clear()
                                    b = rc.build_case(sol, n, mode)
                                    if b is None:
                                        continue
                                    ineqs, eqs = b
                                    ineqs = rc.substitute(
                                        eqs, ineqs)
                                    res = lp_min_delta_f(ineqs)
                                    if res[0] == 'infeasible':
                                        stats['infeas'] += 1
                                    elif res[0] == 'unbounded':
                                        stats['unb'] += 1
                                    else:
                                        stats['bounded'] += 1
                                        results.append(
                                            (res[1],
                                             (k0, k1, k2, k3),
                                             (i0, i1, i2, i3)))
                                sol[3] = None
                            sol[2] = None
                        sol[1] = None
                    sol[0] = None
                    if stats['leaves'] > max_leaves:
                        break
                if stats['leaves'] > max_leaves:
                    break
            if stats['leaves'] > max_leaves:
                break
        if stats['leaves'] > max_leaves:
            break
    print(f'mode={mode} signatures={stats["sig"]} '
          f'leaves={stats["leaves"]} '
          f'tri_pruned={stats["tri_pruned"]} '
          f'infeasible={stats["infeas"]} bounded={stats["bounded"]} '
          f'unbounded={stats["unb"]} time={time.time()-t0:.0f}s')
    if results:
        results.sort(key=lambda x: x[0])
        import collections
        hist = collections.Counter(round(r[0], 3) for r in results)
        print('min-δ histogram:', dict(sorted(hist.items())))
        print('lowest 10 skeletons:')
        for r in results[:10]:
            print(f'   minδ={r[0]:.4f} sig={r[1]} qidx={r[2]}')

if __name__ == '__main__':
    main()
