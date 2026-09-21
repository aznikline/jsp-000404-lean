"""Deletion-based minimal infeasible support (MUS) extraction.

For each skeleton whose float-LP min delta equals the target,
greedily delete ORIG constraints one at a time: a constraint is
permanently removed when the remaining system still forces
delta >= target.  The surviving support is canonicalized under S4
vertex relabeling and clustered.

This clusters the *support topology* (which fan equalities,
triangle equalities, angle bounds, nonnegativity bounds are needed)
rather than the LP's degenerate dual coefficients.

Usage: python3 mus.py k0 k1 k2 k3 [target] [max_kept] [max_skel]
  e.g. python3 mus.py 3 2 2 1 0.5 300
"""
import sys, json, re, time
sys.path.insert(0, '.')
from itertools import permutations
import remainder_check as rc
import seidel_lp
import skeleton_enum as sen
from canonical_cert import lp_min_delta_f, parse_desc, canon, apply_perm

DELTA = rc.DELTA
CONST = rc.CONST
n = 4

# δ domain bounds stay fixed: they define the regime, not the debt.
FIXED = frozenset({'δ≥0', 'δ<1'})

def min_delta_with_skip(sol, skip):
    rc.ORIG.clear()
    b = rc.build_case(sol, n, 'A', skip=skip)
    if b is None:
        return ('infeasible', None)
    ineqs, eqs = b
    ineqs = rc.substitute(eqs, ineqs)
    return lp_min_delta_f(ineqs)

def all_descs(sol):
    """ORIG descs for the full case, in registration order."""
    rc.ORIG.clear()
    rc.build_case(sol, n, 'A')
    return [d for d, _, _ in rc.ORIG]

def mus(sol, target, eps=1e-9):
    """Greedy single-pass deletion MUS.  Returns surviving descs."""
    full = set(all_descs(sol))
    alive = full - FIXED
    for d in sorted(full - FIXED):
        if d not in alive:
            continue
        st = min_delta_with_skip(sol, (full - alive) | {d})
        # infeasible subsystem is even tighter → d still deletable;
        # deletable iff δ < target is still impossible.
        if st[0] == 'infeasible' or (
                st[0] == 'bounded' and st[1] >= target - eps):
            alive.discard(d)
    return alive

def main():
    ks = tuple(int(x) for x in sys.argv[1:5]) or (3, 2, 2, 1)
    target = float(sys.argv[5]) if len(sys.argv) > 5 else 0.5
    max_kept = int(sys.argv[6]) if len(sys.argv) > 6 else 200
    max_skel = int(sys.argv[7]) if len(sys.argv) > 7 else 10**9
    VV = sen.build_VV(ks, n)
    sigvars, sig = sen.build_signatures(VV)
    t0 = time.time()
    total = kept = 0
    clusters = {}
    for sol, idxs, sigkey in sen.gen_cases(ks, n, VV, sigvars, sig):
        total += 1
        if total > max_skel or kept >= max_kept:
            break
        rc.ORIG.clear()
        b = rc.build_case(sol, n, 'A')
        if b is None:
            continue
        ineqs, eqs = b
        ineqs = rc.substitute(eqs, ineqs)
        st = lp_min_delta_f(ineqs)
        if st[0] != 'bounded' or abs(st[1] - target) > 1e-9:
            continue
        kept += 1
        core = mus(sol, target)
        toks = [parse_desc(d) for d in sorted(core)]
        key = canon([(t, '') for t in toks])
        cl = clusters.setdefault(key, {'count': 0, 'reps': []})
        cl['count'] += 1
        if len(cl['reps']) < 3:
            cl['reps'].append({'idxs': idxs, 'sig': sigkey,
                               'descs': sorted(core)})
        if kept % 20 == 0:
            print(f'  {kept} MUS / {total} leaves, '
                  f'{len(clusters)} clusters, '
                  f'{time.time()-t0:.0f}s', flush=True)
    print(f'\nkept={kept} leaves={total} clusters={len(clusters)} '
          f'time={time.time()-t0:.0f}s')
    ranked = sorted(clusters.items(), key=lambda kv: -kv[1]['count'])
    out = []
    for i, (key, cl) in enumerate(ranked):
        cnt = {}
        for t, w in key:
            cnt[t[0]] = cnt.get(t[0], 0) + 1
        print(f'cluster {i}: count={cl["count"]} size={len(key)} '
              f'{dict(sorted(cnt.items()))}')
        out.append({'rank': i, 'count': cl['count'],
                    'key': [list(t) for t, w in key],
                    'reps': cl['reps']})
    fn = f'mus_clusters_ks{"".join(map(str, ks))}_{target}.json'
    with open(fn, 'w') as f:
        json.dump(out, f, indent=1)
    print(f'-> {fn}')

if __name__ == '__main__':
    main()
