"""Adversarial CEGIS over deficit profiles for generic s, mode A.

For each deficit profile d with 2 < W(d) <= band:
  enumerate consistent signatures; within each signature enumerate
  leaves up to leaf_cap; float-LP min delta per skeleton.

  * any skeleton with min_delta < thresh -> COUNTEREXAMPLE
    (profile realizable below the low-regime boundary)
  * skeletons near target are kept for MUS analysis.

Usage: generic_cegis.py n s [band] [leaf_cap] [max_sigs]
"""
import sys, json, time
sys.path.insert(0, '.')
from itertools import combinations
import generic_model as gm
import generic_enum as ge
import seidel_lp

CONST, DELTA = gm.CONST, gm.DELTA

def lp_min_delta_f(ineqs):
    present = sorted({v for q in ineqs for v in q.a if v != CONST},
                     key=str)
    if DELTA not in present:
        present.append(DELTA)
    idx = {v: t for t, v in enumerate(present)}
    nv = len(present)
    cons = [([float(q.a.get(v, 0)) for v in present],
             float(q.b) - float(q.a.get(CONST, 0)))
            for q in ineqs]
    obj = [0.0] * nv
    obj[idx[DELTA]] = -1.0
    r = seidel_lp.lp_max(nv, cons, obj, [(0.0, 1.0)] * nv)
    if r[0] == 'infeasible':
        return ('infeasible', None)
    if r[0] == 'unbounded':
        return ('unbounded', None)
    return ('bounded', -r[1])

def deficit_profiles(n, s, lo=2.0, hi=2.25):
    """Non-increasing d-tuples, d_i >= 0, k_i = n-1-d_i >= 0,
    with lo < W(d) <= hi."""
    out = []

    def rec(pos, lo_k, cur):
        if pos == s:
            if all(x >= 0 for x in cur):
                W = sum(2.0 ** (-d) for d in cur)
                if lo < W <= hi:
                    out.append(tuple(cur))
            return
        for d in range(lo_k, n):
            cur.append(d)
            rec(pos + 1, d, cur)
            cur.pop()

    rec(0, 0, [])
    return out

def scan_profile(ks, n, s, thresh, leaf_cap, max_sigs,
                 collect=20, per_sig=150):
    VV = ge.build_VV(ks, n, s)
    sigvars = ge.build_sigvars(VV, s)
    reps = [{k: VV[i][idxs[0]] for k, idxs in sv.items()}
            for i, sv in enumerate(sigvars)]
    keys = [list(sv) for sv in sigvars]
    ch = [None] * s
    best = [None]
    cex = [None]
    boundary = []
    leaves = sigs = 0
    tris = list(combinations(range(s), 3))

    def per_sig_leaves():
        """Yield variant-index tuples within current sig choice,
        with triangle pruning, capped at a per-sig stride."""
        import itertools
        buckets = [sigvars[v][ch[v]] for v in range(s)]
        for combo_ in itertools.product(*buckets):
            yield combo_

    def sig_run(v):
        nonlocal sigs, leaves
        for k in keys[v]:
            ch[v] = k
            if all(ge.consistent(ch, reps, s, v, u)
                   for u in range(v)):
                if v == s - 1:
                    sigs += 1
                    # prune: per-sig leaf product capped
                    cnt = 0
                    for sol_idx in per_sig_leaves():
                        cnt += 1
                        if cnt > per_sig:
                            break
                        leaves += 1
                        if leaves > leaf_cap or sigs > max_sigs:
                            return
                        sol = [VV[t][sol_idx[t]] for t in range(s)]
                        if not all(gm.tri_maybe(t, sol, n)
                                   for t in tris):
                            continue
                        gm.ORIG.clear()
                        b = gm.build_case(sol, n, 'A')
                        if b is None:
                            continue
                        ineqs, eqs = b
                        ineqs = gm.substitute(eqs, ineqs)
                        st = lp_min_delta_f(ineqs)
                        if st[0] == 'bounded':
                            md = st[1]
                            if best[0] is None or md < best[0]:
                                best[0] = md
                            if abs(md - thresh) < 1e-9 and \
                                    len(boundary) < collect:
                                boundary.append(list(sol_idx))
                            if md < thresh - 1e-9:
                                cex[0] = list(sol_idx)
                                return
                else:
                    sig_run(v + 1)
            if cex[0] is not None or \
                    sigs > max_sigs or leaves > leaf_cap:
                return

    sig_run(0)
    return dict(min_delta=best[0], leaves=leaves, sigs=sigs,
                boundary=boundary, cex=cex[0])

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    s = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    band = float(sys.argv[3]) if len(sys.argv) > 3 else 2.25
    leaf_cap = int(sys.argv[4]) if len(sys.argv) > 4 else 200000
    max_sigs = int(sys.argv[5]) if len(sys.argv) > 5 else 50000
    profs = deficit_profiles(n, s, 2.0, band)
    print(f'n={n} s={s} band=(2,{band}] profiles={len(profs)}')
    for d in profs:
        ks = [n - 1 - x for x in d]
        W = sum(2.0 ** (-x) for x in d)
        print(f'   d={d} k={tuple(ks)} W={W:.4f}')
    report = []
    t0 = time.time()
    for d in profs:
        ks = [n - 1 - x for x in d]
        W = sum(2.0 ** (-x) for x in d)
        tp = time.time()
        res = scan_profile(ks, n, s, 0.5, leaf_cap, max_sigs)
        md = res['min_delta']
        md_rep = ('INFEASIBLE_LT_1' if md is None or md >= 1 - 1e-9
                  else md)
        cex = res['cex'] is not None
        print(f'd={d} k={tuple(ks)} W={W:.3f}: '
              f'{"*** COUNTEREXAMPLE ***" if cex else "killed"}  '
              f'delta_min={md_rep} leaves={res["leaves"]} '
              f'sigs={res["sigs"]} boundary={len(res["boundary"])} '
              f'({time.time()-tp:.0f}s)', flush=True)
        report.append(dict(deficit=d, ks=ks, W=W, cex=cex,
                           cex_witness=res['cex'],
                           min_delta=res['min_delta'],
                           leaves=res['leaves'], sigs=res['sigs'],
                           boundary=res['boundary']))
    fn = f'gcegis_n{n}s{s}.json'
    with open(fn, 'w') as f:
        json.dump(report, f, indent=1, default=str)
    ncex = sum(1 for r in report if r['cex'])
    print(f'\ncex={ncex} -> {fn} ({time.time()-t0:.0f}s)')

if __name__ == '__main__':
    main()
