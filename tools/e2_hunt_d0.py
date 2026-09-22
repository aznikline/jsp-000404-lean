"""Lane E2 — targeted delta=0-forcing-vertex hunt.

A vertex with  Sq = n - s + 1  forces  Sr = m  i.e. all r = 1 and
delta = 0 exactly (fan: Sr = n + d - Sq <= m).  Any CONSISTENT
skeleton containing such a vertex has free_min <= 0 < 1/2, so no
valid gadget can reach bound 1/2 -> instant T_low counterexample.

We restrict every k_v = 0 vertex to Sq = 1 tuples and run the
guided DFS.  Any leaf found is a counterexample candidate and is
exact-verified.

Usage: python3 e2_hunt_d0.py s n workers secs [band]
"""
import sys, time, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from multiprocessing import Pool
import lane_e_util as le
import e2_util as e2


def hunt(task):
    s, n, d, secs = task
    d = tuple(d)
    ks = le.ks_of_d(n, d)
    k0verts = [v for v in range(s) if ks[v] == 0]
    if not k0verts:
        return None

    d0 = n - s + 1                  # Sq forcing delta = 0
    if d0 < 0:
        return None

    def qr(v, q):
        if ks[v] == 0:
            return sum(q) == d0    # forces delta = 0
        return True

    gen = e2.guided(ks, n, s, mode='feas', max_sols=3,
                    deadline=secs, qrestrict=qr)
    res = dict(d=list(d), W=str(le.W_of_d(d)), k0=k0verts,
               found=[], stats=None)
    for sdat, st in gen:
        if sdat is None:
            res['stats'] = st
            break
        v = e2.verify_candidate(sdat, n, s, d)
        res['found'].append(dict(v, sol=sdat))
    return res


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    n = int(sys.argv[2]) if len(sys.argv) > 2 else s
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    secs = float(sys.argv[4]) if len(sys.argv) > 4 else 60
    band = sys.argv[5] if len(sys.argv) > 5 else 'all'
    profs = [d for d in le.deficit_profiles(n, s)
             if d[-1] == n - 1 and le.W_of_d(d) > 2
             and (band == 'all'
                  or (band == 'mid' and le.W_of_d(d) <= F(5, 2))
                  or (band == 'hi' and le.W_of_d(d) > F(5, 2)))]
    print('W>2 profiles ending in %d: %d' % (n - 1, len(profs)))
    tasks = [(s, n, list(d), secs) for d in profs]
    out, nviol = [], 0
    with Pool(workers) as p:
        for res in p.imap_unordered(hunt, tasks):
            if res is None:
                continue
            out.append(res)
            viol = [f for f in res['found'] if f['viol']]
            nviol += len(viol)
            print(res['d'], res['W'], 'found=%d' % len(res['found']),
                  'VIOL!' if viol else '', res['stats'], flush=True)
            for f in viol:
                print('   ', f, flush=True)
            json.dump(out, open(
                'e2_hunt_d0_s%dn%d.json' % (s, n), 'w'), indent=1,
                default=str)
    print('\ndone, viol=%d' % nviol)


if __name__ == '__main__':
    main()
