"""per-leaf best disjunct-split ordering for the nested-first linarith replay.

For each certificate leaf, builds the scalar model, restricts the disjunctive
constraints to the leaf's unsat core, and measures the DFS decision-tree size
(= number of linarith calls the Lean proof will make) under a few fixed
orderings.  Writes {cert: {key: {'order': [...], 'nodes': n}}} to
tools/n4_orders.json.
"""
import z3, itertools, sys, time, json
sys.path.insert(0, 'tools')
from n4_model import build, sig2_case, sig1_case, em_case, MEDPAIR, P

CERTS = {
 'pair_A':    ([(1,'s2'),(3,'s1')], False),
 'pair_B':    ([(1,'s1'),(3,'s2')], False),
 'triple_A':  ([(1,'s2'),(2,'s1'),(4,'s1')], False),
 'triple_B':  ([(0,'s1'),(2,'s1'),(3,'s2')], False),
 'pair04_em': ([(0,'s2'),(4,'s2')], True),
}

delta, t, d, Dm, p, base, trips = build()

def leaf_ors(cert, key):
    spec, hasem = CERTS[cert]
    Uall, ors = [], {}
    for (r, kind), c in zip(spec, key):
        S = [Dm(r, j) for j in range(5) if j != r]
        U, E = (sig2_case if kind=='s2' else sig1_case)(t[r], S, p, c)
        Uall += U
        for tag, e in E:
            ors[f"E{r}_{tag}"] = e
    if hasem:
        ors['em'] = z3.Or(*[em_case(t, Dm, p, r, w) for r, w in [(0,1),(0,2),(0,3),(4,1),(4,2),(4,3)]])
    for ij, tr in trips.items():
        ors[f"tr{ij[0]}{ij[1]}{ij[2]}"] = tr
    return Uall, ors

ORDS = {
    'T': lambda ns: sorted(ns, key=lambda n: (not n.startswith('tr'), n)),
    'E': lambda ns: sorted(ns, key=lambda n: (n.startswith('tr'), n)),
}

def tree_size(s, orl, budget):
    cnt = [0]
    def disjs(e): return e.children() if z3.is_or(e) else [e]
    def dfs(i):
        cnt[0] += 1
        if cnt[0] > budget: return 'OVER'
        if s.check() == z3.unsat: return None
        if i == len(orl): return 'FAIL'
        for dj in disjs(orl[i]):
            s.push(); s.add(dj); r = dfs(i+1); s.pop()
            if r: return r
        return None
    r = dfs(0)
    return cnt[0], r

def best_order(cert, key):
    cores = json.load(open('tools/n4_cores.json'))
    core = cores[cert][','.join(map(str,key))]
    Uall, ors = leaf_ors(cert, key)
    s = z3.Solver(); s.add(z3.And(*base))
    for tag, e in Uall: s.add(e)
    best = None
    for oname, of in ORDS.items():
        names = [n for n in of(list(ors)) if n in core]
        orl = [ors[n] for n in names]
        budget = (best[0] if best else 500000) + 1
        n, r = tree_size(s, orl, budget)
        if r is None and (best is None or n < best[0]):
            best = (n, oname, names)
    return best

def work(arg):
    cert, keystr = arg
    key = tuple(int(v) for v in keystr.split(','))
    b = best_order(cert, key)
    if b is None:
        return cert, keystr, {'order': None, 'nodes': -1, 'mode': 'FAIL'}
    return cert, keystr, {'order': b[2], 'nodes': b[0], 'mode': b[1]}

if __name__ == '__main__':
    from multiprocessing import Pool
    cores = json.load(open('tools/n4_cores.json'))
    jobs = [(c, k) for c, m in cores.items() for k, v in m.items() if v != 'SAT']
    out = {}
    with Pool(8) as pool:
        for i, (cert, kstr, res) in enumerate(pool.imap_unordered(work, jobs)):
            out.setdefault(cert, {})[kstr] = res
            if i % 50 == 0: print(i, '/', len(jobs), cert, kstr, res['nodes'], flush=True)
    json.dump(out, open('tools/n4_orders.json', 'w'))
    print('done')
