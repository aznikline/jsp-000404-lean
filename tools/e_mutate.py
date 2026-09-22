"""Lane E — mutation explorer over skeletons, relaxed-delta climb.

Objective: relaxed_min_delta (LP with delta>=0, NO delta<1 cap).
  <= 1   : capped-feasible (mode-A consistent skeleton)
  > 1    : 'inf' high-debt case — still a descent gradient
  infeas : truly inconsistent

Mutations are profile-FREE (q-jitter may change kv; the resulting
profile is recomputed after the fact), so the walk roams across
profiles tracking the lowest relaxed min-delta seen per profile.

  W > 2   & relaxed_min < 1/2 -> T_low counterexample
  W > 5/2 & relaxed_min < 1   -> T_high counterexample

Usage: python3 e_mutate.py s steps [seed]
"""
import sys, math, random, time, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le
from e_geom import real_skel, gen_config


def mk_sol(data, n, s):
    return [le.mk_variant(v, tuple(d['order']),
                          dict(d['bits']), tuple(d['qs']), n)
            for v, d in enumerate(data)]


def data_of(sol):
    return [{'v': v, 'order': list(sol[v]['order']),
             'bits': dict(sol[v]['bits']),
             'qs': list(sol[v]['qs'])} for v in range(len(sol))]


def consistent_v(data, v, s):
    """Edge-side consistency of vertex v's signature vs all others."""
    pos = {d: t for t, d in enumerate(data[v]['order'])}
    bits = data[v]['bits']
    for u in range(s):
        if u == v:
            continue
        pou = {d: t for t, d in enumerate(data[u]['order'])}
        bu = data[u]['bits']
        for k in range(s):
            if k == u or k == v:
                continue
            sg_v = 1 if pos[k] > pos[u] else -1
            if bits[k] != bits[u]:
                sg_v = -sg_v
            sg_u = 1 if pou[k] > pou[v] else -1
            if bu[k] != bu[v]:
                sg_u = -sg_u
            if sg_v != -sg_u:
                return False
    return True


def full_consistent(data, s):
    return all(consistent_v(data, v, s) for v in range(s))


def tri_ok(sol, n):
    s = len(sol)
    for t in __import__('itertools').combinations(range(s), 3):
        if not le.gm.tri_maybe(t, sol, n):
            return False
    return True


def mutate(data, n, s, rng, qlists_any):
    d2 = [dict(x, bits=dict(x['bits']), qs=tuple(x['qs']),
               order=tuple(x['order'])) for x in data]
    v = rng.randrange(s)
    op = rng.randrange(3)
    if op == 0:
        o = list(d2[v]['order'])
        i, j = rng.sample(range(s - 1), 2)
        o[i], o[j] = o[j], o[i]
        if d2[v]['bits'].get(o[0], 0) != 0:
            return None
        d2[v]['order'] = tuple(o)
    elif op == 1:
        k = d2[v]['order'][rng.randrange(1, s - 1)]
        d2[v]['bits'][k] = 1 - d2[v]['bits'][k]
    else:
        d2[v]['qs'] = qlists_any[rng.randrange(len(qlists_any))]
    if not consistent_v(d2, v, s):
        return None
    return d2


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    n = s
    rng = random.Random(seed)
    fams = ['collinear', 'collinear2', 'circle', 'cluster',
            'twoarc', 'random']
    qlists_any = sorted({q for kk in range(n)
                         for q in le.gm.q_tuples(kk, n, s - 1)})
    pool = []
    lows = {}
    t0 = time.time()
    # seed: geometry (feasible) + combinatorial samples
    while len(pool) < 30 and time.time() - t0 < 60:
        fam = fams[rng.randrange(len(fams))]
        lam = 1.0 / (n + rng.uniform(0.02, 0.98))
        out = real_skel(gen_config(fam, s, rng), n, lam)
        if out is None:
            continue
        sol, kv = out
        st, lo = le.lp_f_relaxed(sol, n)
        if st == 'bounded':
            pool.append(data_of(sol))
    print('seeded %d skeletons (%.0fs)' % (len(pool), time.time() - t0),
          flush=True)
    tris = list(__import__('itertools').combinations(range(s), 3))
    evals = 0
    for step in range(steps):
        data = pool[rng.randrange(len(pool))]
        d2 = mutate(data, n, s, rng, qlists_any)
        if d2 is None:
            continue
        sol = mk_sol(d2, n, s)
        if not all(le.gm.tri_maybe(t, sol, n) for t in tris):
            continue
        st, lo = le.lp_f_relaxed(sol, n)
        evals += 1
        if st != 'bounded':
            continue
        kv2 = [sum(max(q - 1, 0) for q in sol[v]['qs'])
               for v in range(s)]
        d = tuple(sorted(n - 1 - k for k in kv2))
        W = le.W_of_d(d)
        lof = F(lo).limit_denominator(96)
        # accept into pool with prob ~ downhill pressure
        cur_lo = lows.get(d)
        if cur_lo is None or lof < cur_lo[0]:
            lows[d] = (lof, d2)
            band = 'hi' if W > F(5, 2) else \
                ('mid' if W > 2 else 'lo')
            viol = (band == 'hi' and lof < 1) or \
                (band == 'mid' and lof < F(1, 2))
            print('%snew min d=%s W=%s rmin=%s kv=%s step=%d'
                  % ('*** VIOL ' if viol else '', d, str(W),
                     str(lof), kv2, step), flush=True)
        # drift: keep feasible-ish mutants in the pool
        if lof <= 1.5 or rng.random() < 0.15:
            pool.append(d2)
            if len(pool) > 500:
                pool.pop(rng.randrange(len(pool)))
    print('\nevals=%d profiles=%d (%.0fs)'
          % (evals, len(lows), time.time() - t0))
    for band, cond in (('hi(>5/2)', lambda W: W > F(5, 2)),
                       ('mid(2,5/2]',
                        lambda W: F(2) < W <= F(5, 2)),
                       ('lo', lambda W: W <= 2)):
        rows = [(lof, W, d) for d, (lof, _) in lows.items()
                if cond(W)]
        rows.sort()
        print('  band %s: %d profiles; lowest:' % (band, len(rows)))
        for lof, W, d in rows[:6]:
            print('     rmin=%s W=%s d=%s %s'
                  % (lof, W, d,
                     'FEAS' if lof <= 1 else 'high-debt'))
    json.dump({str(d): (str(lof),) for d, (lof, _) in lows.items()},
              open('lane_e_mutate_s%d.json' % s, 'w'), indent=1)


if __name__ == '__main__':
    main()
