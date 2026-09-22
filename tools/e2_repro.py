"""Lane E2 — compact repro of the wave-2 headline facts.

Run:  python3 e2_repro.py            (from tools/, ~2-3 min)

Checks, all exact (Fraction LP via residual_map.glp_min_delta)
unless marked float:

  R1  s=4 all-k3 profile (0,0,0,0), W=4: gen_cases enumeration ->
      ZERO Lean-consistent skeletons (relaxed_min < 1).
  R2  s=4 mid profile (0,0,2,2), W=5/2: consistent skeletons
      exist; the first ones verify capped=relaxed=free=1/2.
  R3  wave-1 s=6 hi-band seeds are PHANTOMS:
      relaxed_min = 1 (not consistent under 0<=d<1).
  R4  guided DFS finds a consistent s=6 skeleton in a seeded mid
      profile quickly (machinery sanity).
  R5  lane_a6._CAP_CACHE id(ctx) reuse: successive Ctx
      allocations recycle ids (structural poison hazard demo).
  R6  extended evaluator bound <= free_min on sampled s=4
      skeletons (no overcertification).
"""
import sys, gc, json, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le
import e2_util as e2
import generic_enum as ge


def r1():
    print('R1: s=4 (0,0,0,0) W=4 — enumerating all skeletons')
    ks = le.ks_of_d(4, (0, 0, 0, 0))
    VV = ge.build_VV(ks, 4, 4)
    sigvars = ge.build_sigvars(VV, 4)
    tot = cons = 0
    for sol, idxs, sk in ge.gen_cases(ks, 4, 4, VV=VV,
                                      sigvars=sigvars):
        tot += 1
        nv, c, o = e2.float_cons(sol, list(range(4)), 4, 4,
                                 'relaxed')
        st, lo = e2.lp_min_f(nv, c, o)
        if st == 'bounded' and lo < 1 - 1e-7:
            cons += 1
    print('   tested=%d consistent=%d   [expect cons=0]' % (tot, cons))
    return tot, cons


def r2():
    print('R2: s=4 (0,0,2,2) W=5/2 — consistent skeletons @ 1/2')
    ks = le.ks_of_d(4, (0, 0, 2, 2))
    VV = ge.build_VV(ks, 4, 4)
    sigvars = ge.build_sigvars(VV, 4)
    shown = 0
    for sol, idxs, sk in ge.gen_cases(ks, 4, 4, VV=VV,
                                      sigvars=sigvars):
        nv, c, o = e2.float_cons(sol, list(range(4)), 4, 4,
                                 'relaxed')
        st, lo = e2.lp_min_f(nv, c, o)
        if st != 'bounded' or lo >= 1 - 1e-7:
            continue
        mm = e2.mins_exact(sol, 4)
        print('   idxs=%s capped=%s relaxed=%s free=%s'
              % (idxs, mm['capped'][1], mm['relaxed'][1],
                 mm['free'][1]))
        shown += 1
        if shown >= 3:
            break
    return shown


def r3():
    print('R3: wave-1 s=6 hi seeds are phantoms (relaxed_min=1)')
    seeds = json.load(open('lane_e_seeds_s6n6.json'))
    n_ph = n_cons = 0
    for ds, lst in seeds.items():
        d = tuple(map(int, ds[1:-1].split(', ')))
        if le.W_of_d(d) <= F(5, 2):
            continue
        for sd in lst[:1]:
            sol = le.data_to_sol(sd['data'], 6)
            st, lo = e2.relaxed_exact(sol, 6)
            if st == 'bounded' and lo < 1:
                n_cons += 1
            else:
                n_ph += 1
                print('   %s relaxed=%s -> phantom' % (d, lo))
        if n_ph + n_cons >= 5:
            break
    print('   checked %d hi seeds: phantom=%d consistent=%d'
          % (n_ph + n_cons, n_ph, n_cons))


def r4():
    print('R4: guided DFS on s=6 seeded mid profile (0,2,2,2,2,3)')
    ks = le.ks_of_d(6, (0, 2, 2, 2, 2, 3))
    t = time.time()
    for sdat, st in e2.guided(ks, 6, 6, mode='feas', max_sols=1,
                              deadline=60):
        if sdat is None:
            break
        v = e2.verify_candidate(sdat, 6, 6, (0, 2, 2, 2, 2, 3))
        print('   found consistent=%s capped=%s relaxed=%s free=%s'
              ' (%.1fs, nodes=%d)'
              % (v['consistent'], v['capped'], v['relaxed'],
                 v['free'], time.time() - t, st['nodes']))
        break


def r5():
    print('R5: lane_a6._CAP_CACHE id(ctx) reuse')
    import link_graph as lg
    seeds = json.load(open('lane_e_seeds_s6n6.json'))
    sd = list(seeds.values())[0][0]['data']
    ids = []
    for _ in range(6):
        sol = le.data_to_sol(sd, 6)
        ctx = lg.Ctx(sol, 6, 6)
        ids.append(id(ctx))
        del sol, ctx
        gc.collect()
    reused = len(set(ids)) < len(ids)
    print('   ctx ids %s -> reused=%s' % (ids, reused))


def r6():
    print('R6: extended evaluator bound <= free_min (s=4 sample)')
    import lane_a6
    ks = le.ks_of_d(4, (0, 1, 1, 1))
    VV = ge.build_VV(ks, 4, 4)
    sigvars = ge.build_sigvars(VV, 4)
    n = s = 4
    shown = over = 0
    for sol, idxs, sk in ge.gen_cases(ks, n, s, VV=VV,
                                      sigvars=sigvars):
        lane_a6._CAP_CACHE.clear()
        b = lane_a6.enumerate_max_ext(sol, n, s, maxsz=3)
        mm = e2.mins_exact(sol, n)
        fmin = mm['free'][1] if mm['free'][0] == 'bounded' else None
        print('   idxs=%s capped=%s free=%s ext=%s'
              % (idxs, mm['capped'][1], fmin, b))
        if b is not None and fmin is not None and b > fmin:
            over += 1
            print('   *** OVERCERT bound=%s > free=%s' % (b, fmin))
        shown += 1
        if shown >= 3:
            break
    print('   over=%d' % over)


if __name__ == '__main__':
    r1(); r2(); r3(); r4(); r5(); r6()
