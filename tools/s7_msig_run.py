import z3, itertools, time, json, sys
from multiprocessing import Pool
from s7_msig import *

CLASSES = [
    ((0, 1), 2, 'AA_s1_2'), ((0, 1), 5, 'AA_s1_5'),
    ((4, 5), 0, 'AB_s1_0'), ((4, 5), 3, 'AB_s1_3'),
]

def check_combo(job):
    name, spec, combo = job
    delta, t, d, D, p, base, trips = build()
    s = z3.Solver(); s.set("timeout", 60000)
    s.add(base)
    for tr in trips.values(): s.add(tr)
    for (row, kind), c in zip(spec, combo):
        S = [D(row, j) for j in range(P) if j != row]
        U, E = (s7_sig2_case if kind == 's2' else s7_sig1_case)(t[row], S, p, c)
        s.add([e for _, e in U] + [e for _, e in E])
    return name, combo, s.check() == z3.unsat

if __name__ == '__main__':
    tagged = []
    for low, mid, name in CLASSES:
        spec = [(low[0], 's2'), (low[1], 's2'), (mid, 's1')]
        for combo in itertools.product(range(21), range(21), range(6)):
            tagged.append((name, spec, combo))
    t0 = time.time()
    results, sats = {}, {}
    with Pool(8) as pool:
        for name, combo, uns in pool.imap_unordered(check_combo, tagged, chunksize=16):
            results[name] = results.get(name, 0) + int(uns)
            if not uns:
                sats.setdefault(name, []).append(combo)
            done = sum(results.values()) + sum(len(v) for v in sats.values())
            if done % 2000 == 0:
                print(f'...{done}/10584 ({time.time()-t0:.0f}s)', flush=True)
    for name, _, nm in CLASSES:
        nm_ = nm
        print(nm_, results.get(nm_, 0), 'unsat of 2646;',
              len(sats.get(nm_, [])), 'sat/unk', flush=True)
        for c in sats.get(nm_, [])[:20]:
            print('   SAT', c)
    json.dump({k: [list(x) for x in v] for k, v in sats.items()},
              open('s7_msig_sats.json', 'w'))
    print('total', time.time() - t0)
