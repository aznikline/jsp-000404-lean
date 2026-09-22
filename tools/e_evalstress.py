"""Lane E — gadget evaluator stress: enumerate_max vs LP.

For sampled skeletons, compare the pure-enumerator best bound against
  (a) capped LP min-delta   (consistent skeletons: bound must be <= lo
      for soundness, >= lo would be OVERCOUNT = unsound gadget)
  (b) relaxed LP min-delta  (for capped-infeasible 'inf' skeletons:
      bound > relaxed_min would be overcount; bound < relaxed_min is
      undercount = gadget-family gap)

Usage: python3 e_evalstress.py s per_profile [seed]
"""
import sys, itertools, time, random, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le


def enumerate_budgeted(sol, n, s, max_len=3, fan_cap=80,
                       pivots=None, seed=0):
    """Budget-limited link_graph enumerate_max for s>=5.
    Explores: pure gadget + paths of length<=max_len through each
    pivot (open and closed) x a random subset of fan assignments."""
    rng = random.Random(seed)
    ctx = le.lg.Ctx(sol, n, s)
    best = le.lg.pure_gadget(ctx)
    fas = list(le.lg.fan_assignments(s))
    if len(fas) > fan_cap:
        fas = [fas[0]] + rng.sample(fas[1:], fan_cap - 1)
    pivots = range(s) if pivots is None else pivots
    for h in pivots:
        outer = [v for v in range(s) if v != h]
        for r_ in range(0, min(max_len, len(outer)) + 1):
            perms = [()] if r_ == 0 else \
                itertools.permutations(outer, r_)
            for perm in perms:
                for closed in (False, True):
                    for edges in le.lg.edge_lists(list(perm), closed):
                        for fa in fas:
                            res = le.lg.eval_chain(ctx, h, edges, fa)
                            if res is not None and (
                                    best is None or
                                    res['bound'] > best['bound']):
                                best = res
    return best


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    per_prof = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    n = s
    rng = random.Random(seed)
    profs = le.deficit_profiles(n, s)
    over, under, match, inf_nogadget = [], [], 0, []
    tested = 0
    t0 = time.time()
    for d in profs:
        W = le.W_of_d(d)
        ks = le.ks_of_d(n, d)
        VV = le.ge.build_VV(ks, n, s)
        sigvars = le.ge.build_sigvars(VV, s)
        cnt = 0
        for sol, idxs, sk in le.ge.gen_cases(ks, n, s, VV=VV,
                                             sigvars=sigvars):
            if cnt >= per_prof:
                break
            cnt += 1
            st, lo = le.lp_x(sol, n)
            best = le.lg.enumerate_max(sol, n, s)
            bb = None if best is None else best['bound']
            tested += 1
            if st == 'bounded':
                if bb is None or bb < lo:
                    under.append(dict(d=d, idxs=idxs, lo=str(lo),
                                      bb=None if bb is None
                                      else str(bb)))
                    print('UNDER d=%s idxs=%s lo=%s bb=%s'
                          % (d, idxs, lo, bb), flush=True)
                elif bb > lo:
                    over.append(dict(d=d, idxs=idxs, lo=str(lo),
                                     bb=str(bb)))
                    print('*** OVER d=%s idxs=%s lo=%s bb=%s'
                          % (d, idxs, lo, bb), flush=True)
                else:
                    match += 1
            else:
                st2, lo2, _ = le.lp_relaxed(sol, n)
                if st2 == 'bounded':
                    if bb is not None and bb > lo2:
                        over.append(dict(d=d, idxs=idxs,
                                         relaxed=str(lo2),
                                         bb=str(bb)))
                        print('*** OVER-INF d=%s idxs=%s rmin=%s '
                              'bb=%s' % (d, idxs, lo2, bb),
                              flush=True)
                    elif bb is None or bb < lo2:
                        under.append(dict(d=d, idxs=idxs,
                                          relaxed=str(lo2),
                                          bb=None if bb is None
                                          else str(bb)))
                        print('UNDER-INF d=%s idxs=%s rmin=%s bb=%s'
                              % (d, idxs, lo2, bb), flush=True)
                    else:
                        match += 1
                else:
                    if bb is None:
                        inf_nogadget.append(dict(d=d, idxs=idxs))
                    else:
                        match += 1
        print('d=%s W=%s done (%d tested, %.0fs)'
              % (d, str(W), tested, time.time() - t0), flush=True)
    print('\ntested=%d match=%d over=%d under=%d inf_no_gadget=%d'
          % (tested, match, len(over), len(under),
             len(inf_nogadget)))
    for r in over + under:
        print('  ', r)
    json.dump(dict(over=over, under=under,
                   inf_nogadget=inf_nogadget),
              open('lane_e_evalstress_s%d.json' % s, 'w'), indent=1)


if __name__ == '__main__':
    main()
