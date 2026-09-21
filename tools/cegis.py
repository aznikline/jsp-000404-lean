"""CEGIS over violating exponent profiles.

For a given (n, s, regime), enumerate every sorted exponent profile
k = (k_1 ≥ … ≥ k_s) with Σ 2^{k_i} > SendovCap, then for each profile
enumerate its realizable skeletons and ask the mode-A LP:

  * any skeleton with min δ < threshold  → COUNTEREXAMPLE (report)
  * all infeasible or min δ ≥ threshold  → profile killed; record the
    best (lowest) min-δ witness for certificate templating.

SendovCap:  low regime  (δ < 1/2):   Σ 2^{k_i} ≤ 2^n
            high regime (δ ≥ 1/2):   Σ 2^{k_i} ≤ 2^n + 2^{n-2}

Usage: python3 cegis.py [n] [s] [low|high] [max_leaves_per_profile]
"""
import sys, json, time, itertools
sys.path.insert(0, '.')
import remainder_check as rc
import skeleton_enum as se
import seidel_lp as sl

def lp_min_f(ineqs):
    present = sorted({v for q in ineqs for v in q.a
                      if v != rc.CONST}, key=str)
    if rc.DELTA not in present:
        present.append(rc.DELTA)
    cons = [([float(q.a.get(v, 0)) for v in present],
             float(q.b) - float(q.a.get(rc.CONST, 0)))
            for q in ineqs]
    obj = [0.0] * len(present)
    obj[present.index(rc.DELTA)] = -1.0
    r = sl.lp_max(len(present), cons, obj,
                  [(0.0, 1.0)] * len(present))
    if r[0] == 'infeasible':
        return ('infeasible', None)
    if r[0] == 'unbounded':
        return ('unbounded', None)
    return ('bounded', -r[1])

def violating_profiles(n, s, cap):
    """Sorted desc exponent profiles over s vertices, k_i ≤ n-1,
    with Σ 2^{k_i} > cap."""
    out = []
    def rec(pos, lo):
        if pos == s:
            ks = tuple(sorted(cur, reverse=True))
            if sum(2 ** k for k in ks) > cap:
                out.append(ks)
            return
        for k in range(lo, -1, -1):
            cur.append(k)
            rec(pos + 1, k)
            cur.pop()
    cur = []
    rec(0, n - 1)
    return sorted(set(out), key=lambda ks: -sum(2 ** k for k in ks))

def scan_profile(ks, n, mode, thresh, max_leaves, t_deadline):
    """Returns dict(status, min_delta, witness, leaves, sigs).
    status: 'counterexample' | 'killed' | 'timeout'"""
    VV = se.build_VV(ks, n)
    sigvars, sig = se.build_signatures(VV)
    leaves = 0
    best = None           # (minδ, idxs, sigkey)
    for k0, k1, k2, k3 in se.consistent_signatures(sigvars, sig):
        sigkey = (k0, k1, k2, k3)
        sol = [None] * 4
        for i0 in sigvars[0][k0]:
            sol[0] = VV[0][i0]
            for i1 in sigvars[1][k1]:
                sol[1] = VV[1][i1]
                for i2 in sigvars[2][k2]:
                    sol[2] = VV[2][i2]
                    if not rc.tri_maybe((0, 1, 2), sol, n):
                        continue
                    for i3 in sigvars[3][k3]:
                        sol[3] = VV[3][i3]
                        leaves += 1
                        if leaves > max_leaves:
                            return dict(status='timeout',
                                        min_delta=best[0] if best
                                        else None,
                                        witness=best, leaves=leaves)
                        if not all(rc.tri_maybe(t, sol, n)
                                   for t in ((0, 1, 3), (0, 2, 3),
                                             (1, 2, 3))):
                            continue
                        rc.ORIG.clear()
                        b = rc.build_case(sol, n, mode)
                        if b is None:
                            continue
                        ineqs, eqs = b
                        ineqs = rc.substitute(eqs, ineqs)
                        r = lp_min_f(ineqs)
                        if r[0] == 'bounded':
                            if best is None or r[1] < best[0]:
                                best = (r[1], (i0, i1, i2, i3),
                                        sigkey)
                            if r[1] < thresh:
                                return dict(
                                    status='counterexample',
                                    min_delta=r[1],
                                    witness=(r[1],
                                             (i0, i1, i2, i3),
                                             sigkey),
                                    leaves=leaves)
                    sol[2] = None
                sol[1] = None
            sol[0] = None
    return dict(status='killed',
                min_delta=best[0] if best else None,
                witness=best, leaves=leaves)

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    s = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    regime = sys.argv[3] if len(sys.argv) > 3 else 'low'
    max_leaves = int(sys.argv[4]) if len(sys.argv) > 4 else 3000000
    cap = (1 << n) if regime == 'low' else (1 << n) + (1 << (n - 2))
    thresh = 0.5 if regime == 'low' else 1.0
    profs = violating_profiles(n, s, cap)
    print(f'n={n} s={s} regime={regime} cap=Σ2^k≤{cap} '
          f'violating profiles={len(profs)}')
    for ks in profs:
        d = [n - 1 - k for k in ks]
        W = sum(2.0 ** (-x) for x in d)
        print(f'   {ks}  d={tuple(d)}  W={W:.4f}  '
              f'Σ2^k={sum(2**k for k in ks)}')
    print()
    report = []
    t0 = time.time()
    for ks in profs:
        tp = time.time()
        res = scan_profile(list(ks), n, 'A', thresh, max_leaves, t0)
        el = time.time() - tp
        tag = {'counterexample': '*** COUNTEREXAMPLE ***',
               'killed': 'killed', 'timeout': 'TIMEOUT'}[res['status']]
        md = res['min_delta']
        # δ ∈ [0,1): minδ ≥ 1 means infeasible for every legal δ —
        # report as INFEASIBLE_LT_1, not a numeric extremizer.
        md_rep = ('INFEASIBLE_LT_1' if md is None or md >= 1 - 1e-9
                  else md)
        d = [n - 1 - k for k in ks]
        W = sum(2.0 ** (-x) for x in d)
        print(f'{ks} d={tuple(d)} W={W:.3f}: {tag}  '
              f'delta_min={md_rep} leaves={res["leaves"]} '
              f'({el:.0f}s)', flush=True)
        report.append(dict(profile=list(ks), deficit=d,
                           normalized_weight=W, delta_min=md_rep,
                           **res))
        if res['status'] == 'counterexample':
            print('   witness:', res['witness'])
    fn = f'cegis_n{n}s{s}_{regime}.json'
    with open(fn, 'w') as f:
        json.dump(report, f, indent=1, default=str)
    cex = [r for r in report if r['status'] == 'counterexample']
    print(f'\n{len(cex)} counterexamples; report -> {fn} '
          f'({time.time()-t0:.0f}s)')

if __name__ == '__main__':
    main()
