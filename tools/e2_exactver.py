"""Lane E2 — exact re-verification of consistent skeletons.

For every profile where a campaign found consistent leaves, re-run
feas-mode guided DFS and exact-verify (capped, relaxed, free via
Fraction LP) every leaf found.  Records the exact free-minimum set.

Usage: python3 e2_exactver.py <campaign_json> s n [workers] [secs]
Writes e2_exactver_s{S}n{N}.json.
"""
import sys, json, time
sys.path.insert(0, '.')
from fractions import Fraction as F
from multiprocessing import Pool
import lane_e_util as le
import e2_util as e2


def job(task):
    s, n, d, secs = task
    d = tuple(d)
    ks = le.ks_of_d(n, d)
    out = dict(d=list(d), W=str(le.W_of_d(d)), sols=[])
    for sdat, st in e2.guided(ks, n, s, mode='feas', max_sols=10,
                              deadline=secs):
        if sdat is None:
            break
        v = e2.verify_candidate(sdat, n, s, d)
        out['sols'].append({k: (str(v[k]) if not isinstance(
            v[k], (int, bool, type(None))) else v[k])
            for k in ('consistent', 'capped', 'relaxed', 'free',
                      'viol')})
        out['sols'][-1]['data'] = sdat
    return out


def main():
    cj = sys.argv[1]
    s = int(sys.argv[2]); n = int(sys.argv[3])
    workers = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    secs = float(sys.argv[5]) if len(sys.argv) > 5 else 15
    rows = json.load(open(cj))
    profs = [r['d'] for r in rows if r['feas']['consistent'] > 0]
    print('re-verifying %d profiles' % len(profs), flush=True)
    res = []
    with Pool(workers) as p:
        for row in p.imap_unordered(
                job, [(s, n, d, secs) for d in profs]):
            res.append(row)
            fs = set(x['free'] for x in row['sols'])
            vl = sum(1 for x in row['sols'] if x['viol'])
            print('d=%s W=%s sols=%d free=%s viol=%d'
                  % (row['d'], row['W'], len(row['sols']), fs, vl),
                  flush=True)
            json.dump(res, open('e2_exactver_s%dn%d.json' % (s, n),
                                'w'), indent=1)
    allf = set(x['free'] for r in res for x in r['sols'])
    allv = sum(1 for r in res for x in r['sols'] if x['viol'])
    print('\ndone: %d profiles, free-min set=%s, viol=%d'
          % (len(res), allf, allv))


if __name__ == '__main__':
    main()
