"""Lane E — per-profile hill climber minimizing relaxed min-delta.

Objective: relaxed_min_delta (LP without the delta<1 cap).
  <= 1    : capped-feasible; the recorded min-delta is the level/2.
  > 1     : capped-infeasible 'high-debt' skeleton (still gives a
            descent gradient toward feasibility!).
  infeas  : truly inconsistent — discarded.

Mutations preserve each vertex's exponent kv (q-jitter draws from
q_tuples with the same ktarget; order/bit mutations keep qs), so a
climb stays inside one deficit profile d.

A profile minimum below the band requirement is a counterexample:
  W > 2   & relaxed_min < 1/2  -> T_low dead
  W > 5/2 & relaxed_min < 1    -> T_high dead

Usage: python3 e_climb.py s d0,d1,... iters restarts [seed]
"""
import sys, math, random, time, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le


def side_of(order, bits):
    pos = {d: t for t, d in enumerate(order)}
    side = {}
    for j in order:
        for k in order:
            if k == j:
                continue
            sgn = 1 if pos[k] > pos[j] else -1
            if bits[k] != bits[j]:
                sgn = -sgn
            side[(j, k)] = sgn
    return side


def sig_ok_against(sigs, v, cand, s):
    side_v = cand[2]
    for u in range(s):
        if u == v or sigs[u] is None:
            continue
        su = sigs[u][2]
        for k in range(s):
            if k == u or k == v:
                continue
            if side_v[(u, k)] != -su[(v, k)]:
                return False
    return True


def climb_profile(d, n, s, iters, restarts, rng, seeds=None):
    ks = le.ks_of_d(n, d)
    smp = le.Sampler(ks, n, s, rng)
    tris = smp.tris
    qlists_all = [sorted(le.gm.q_tuples(kk, n, s - 1))
                  for kk in range(n)]
    best = [None]   # (relaxed_min, sol)
    stats = dict(samples=0, mut=0, acc=0, seeds=0)

    def eval_sol(sol):
        st, lo = le.lp_f_relaxed(sol, n)
        if st != 'bounded':
            return None
        return lo

    def tri_ok_partial(sol, v):
        for t in tris:
            if v in t and all(sol[x] is not None for x in t):
                if not le.gm.tri_maybe(t, sol, n):
                    return False
        return True

    seed_sols = []
    if seeds:
        for sd in seeds:
            try:
                seed_sols.append(le.data_to_sol(sd['data'], n))
            except Exception:
                pass
        stats['seeds'] = len(seed_sols)

    for rs in range(restarts):
        if seed_sols:
            sol0 = seed_sols[rs % len(seed_sols)]
            sol = [le.mk_variant(v, vv['order'], vv['bits'], vv['qs'],
                                 n)
                   for v, vv in enumerate(sol0)]
        else:
            sol = smp.sample()
        if sol is None:
            continue
        stats['samples'] += 1
        cur = eval_sol(sol)
        if cur is None:
            continue
        # per-vertex kv fixed by qs -> profile-preserving jitter lists
        kvv = [sum(max(q - 1, 0) for q in sol[v]['qs'])
               for v in range(s)]
        qlists = [qlists_all[min(k, n - 1)] for k in kvv]
        if best[0] is None or cur < best[0][0]:
            best[0] = (cur, le.sol_to_data(sol))
        # hill climb
        for it in range(iters):
            stats['mut'] += 1
            v = rng.randrange(s)
            op = rng.randrange(3)
            vv = sol[v]
            if op == 0:      # order swap (keep bits by label)
                o = list(vv['order'])
                i, j = rng.sample(range(s - 1), 2)
                o[i], o[j] = o[j], o[i]
                if vv['bits'].get(o[0], 0) != 0:
                    continue
                norder, nbits, nqs = tuple(o), vv['bits'], vv['qs']
            elif op == 1:    # bit flip
                k = vv['order'][rng.randrange(1, s - 1)]
                nbits = dict(vv['bits'])
                nbits[k] = 1 - nbits[k]
                norder, nqs = vv['order'], nbits
            else:            # q redraw (same kv)
                norder, nbits = vv['order'], vv['bits']
                nqs = qlists[v][rng.randrange(len(qlists[v]))]
            # signature consistency of v vs the rest
            pos = {dd: t for t, dd in enumerate(norder)}
            side_v = {}
            for j in norder:
                for k in norder:
                    if k == j:
                        continue
                    sg = 1 if pos[k] > pos[j] else -1
                    if nbits[k] != nbits[j]:
                        sg = -sg
                    side_v[(j, k)] = sg
            okk = True
            for u in range(s):
                if u == v:
                    continue
                su = sol[u]['side']
                for k in range(s):
                    if k == u or k == v:
                        continue
                    if side_v[(u, k)] != -su[(v, k)]:
                        okk = False
                        break
                if not okk:
                    break
            if not okk:
                continue
            newv = le.mk_variant(v, norder, dict(nbits),
                                 tuple(nqs), n)
            old = sol[v]
            sol[v] = newv
            if not tri_ok_partial(sol, v):
                sol[v] = old
                continue
            new = eval_sol(sol)
            if new is None:
                sol[v] = old
                continue
            if new <= cur + 1e-9:      # accept sideways/downhill
                cur = new
                stats['acc'] += 1
                if best[0] is None or new < best[0][0]:
                    best[0] = (new, le.sol_to_data(sol))
            else:
                sol[v] = old
    return best[0], stats


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    n = s
    args = sys.argv[2:]
    if args and args[0] == 'band':
        band = args[1]
        iters = int(args[2]) if len(args) > 2 else 40
        restarts = int(args[3]) if len(args) > 3 else 30
        seed = int(args[4]) if len(args) > 4 else 0
        profs = [d for d in le.deficit_profiles(n, s)
                 if (F(5, 2) < le.W_of_d(d) if band == 'hi'
                     else F(2) < le.W_of_d(d) <= F(5, 2)
                     if band == 'mid' else le.W_of_d(d) <= 2)]
    else:
        d = tuple(int(x) for x in args[0].split(','))
        iters = int(args[1]) if len(args) > 1 else 40
        restarts = int(args[2]) if len(args) > 2 else 30
        seed = int(args[3]) if len(args) > 3 else 0
        profs = [d]
    rng = random.Random(seed)
    seedlib = {}
    sf = 'lane_e_seeds_s%dn%d.json' % (s, n)
    try:
        import json as _json
        seedlib = _json.load(open(sf))
    except OSError:
        pass
    t0 = time.time()
    results = []
    for d in profs:
        W = le.W_of_d(d)
        seeds = seedlib.get(str(tuple(d)))
        best, stats = climb_profile(d, n, s, iters, restarts, rng,
                                    seeds=seeds)
        if best is None:
            print('d=%s W=%s : no consistent skeleton found (%s)'
                  % (d, W, stats), flush=True)
            results.append(dict(d=list(d), W=str(W), min=None))
            continue
        lo, sdat = best
        lof = F(lo).limit_denominator(96)
        viol = (W > F(5, 2) and lof < 1) or \
               (W > 2 and lof < F(1, 2))
        print('d=%s W=%s : relaxed_min=%s samples=%d acc=%d%s'
              % (d, str(W), str(lof), stats['samples'],
                 stats['acc'], '  *** VIOLATION ***' if viol
                 else ''), flush=True)
        results.append(dict(d=list(d), W=str(W), min=str(lof),
                            viol=viol, sol=sdat if viol else None))
        if viol:
            json.dump(results[-1],
                      open('lane_e_climb_cex_%s.json'
                           % ''.join(map(str, d)), 'w'), indent=1)
    json.dump(results,
              open('lane_e_climb_s%d.json' % s, 'w'), indent=1)
    nv = sum(1 for r in results if r.get('viol'))
    print('\nprofiles=%d viol=%d (%.0fs)'
          % (len(results), nv, time.time() - t0))


if __name__ == '__main__':
    main()
