"""Extract decision trees for the S7 between-class cert `s7_BTem`.

Spec: two s2 rows at theta-ranks 0 and 5 of the P=6 model, plus the
residual-emission disjunction (8 arms):

    OR_{r in 1..4}  t0 + p - 1 < d(0,r)   (lo-end emission, upper strip)
                 OR  d(r,5) < t5 + 1       (hi-end emission, lower strip)

The impossible sibling disjuncts (d(0,r) < t0+1, d(r,5) > t5+p-1) are
already killed by the corridor and need not enter the tree.

Tree: same format as s7_extract_trees; the em node carries
emitmeta = di so the leaf emitter can map arm index -> chord slot.
"""
import z3, itertools, json, sys, time, os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s7_canon import (build, nb, sig2_of_class, CANON2_ORDER)
from s7_extract_trees import disjs, linear_strip, count_nodes

P = 6
CASES2 = [c for c in CANON2_ORDER if c != 'M_II']


def btem_env(combo):
    """ground, ors for s2@{0,5} + em.  em is an 8-arm or-node."""
    delta, t, d, D, p, base, trips = build(P)
    ground = [('hplo', delta >= 0), ('hphi', delta < 1),
              ('ht0b', t[0] >= 0), ('htPb', t[P - 1] <= delta)]
    for i in range(P - 1):
        ground.append((f'ht{i}{i+1}', t[i] < t[i + 1]))
    for i in range(P):
        for j in range(i + 1, P):
            ground.append((f'hc{i}{j}',
                           z3.And(t[i] + 1 <= d[(i, j)],
                                  d[(i, j)] <= p - 1 + t[j])))
    ors = {}
    for (r, kind), c in zip([(0, 's2'), (5, 's2')], combo):
        S = [D(r, j) for j in range(P) if j != r]
        U, E = sig2_of_class(P, t[r], S, p, c)
        for ci, (tag, e) in enumerate(U):
            ground.append((f'u{r}{tag}{ci}', e))
        for ei, (tag, e) in enumerate(E):
            ors[f'E{r}_{tag}{ei}'] = (tag, r, e)
    em = z3.Or(*[z3.Or(D(0, r) > t[0] + p - 1, D(r, 5) < t[5] + 1)
                 for r in range(1, 5)])
    ors['em'] = ('em', 0, em)
    for ij, tr in trips.items():
        ors[f'tr{ij[0]}{ij[1]}{ij[2]}'] = ('tr', ij, tr)
    return ground, ors


def build_tree(combo, order, budget_nodes=4_000_000):
    delta, t, d, D, p, base, trips = build(P)
    ground, ors = btem_env(combo)
    s = z3.Solver()
    slin = z3.Solver()
    for n, e in ground:
        s.assert_and_track(e, n)
        slin.assert_and_track(e, n)
    counter = itertools.count()
    nchords = P - 1
    Srows = {r: [D(r, j) for j in range(P) if j != r] for r in (0, 5)}

    def push_disj(name, typ, r, dj, tag):
        s.assert_and_track(dj, tag)
        for j, ch in enumerate(linear_strip(dj)):
            slin.assert_and_track(ch, f'{tag}c{j}')

    def pair_atoms(expr):
        a = expr.children()[0] if z3.is_and(expr) else expr
        return a.children()[0], a.children()[1]

    def dfs(queue, qi):
        nd = next(counter)
        if nd > budget_nodes:
            return ['OVER']
        if slin.check() == z3.unsat:
            return ['term', sorted(str(u) for u in slin.unsat_core())]
        if s.check() == z3.unsat and qi >= len(queue):
            return ['NEEDS_SPLIT']
        if qi >= len(queue):
            return ['FAIL']
        name, typ, r, orexp, emitmeta = queue[qi]
        kids = []
        for di, dj in enumerate(disjs(orexp)):
            s.push(); slin.push()
            push_disj(name, typ, r, dj, f'N{nd}')
            front = []
            if typ in ('bigk', 'sml'):
                ci = 3 if typ == 'bigk' else 2
                x, y = pair_atoms(dj)
                for z_ in range(nchords):
                    front.append(('nbz', 'nbz', r,
                                  z3.Or(Srows[r][z_] <= x,
                                        y <= Srows[r][z_]),
                                  (nd, di, ci, z_)))
            q2 = queue[:qi + 1] + front + queue[qi + 1:]
            kids.append(dfs(q2, qi + 1))
            s.pop(); slin.pop()
            if kids and kids[-1][0] in ('FAIL', 'OVER', 'NEEDS_SPLIT'):
                return ['FAIL']
        return ['node', nd, (typ, r, name, emitmeta), kids]

    queue = [(n, ors[n][0], ors[n][1], ors[n][2], None) for n in order]
    return dfs(queue, 0)


def main():
    out = {}
    t0 = time.time()
    fails = []
    for ca, cb in itertools.product(CASES2, repeat=2):
        combo = (ca, cb)
        ground, ors = btem_env(combo)
        rest = sorted((n for n in ors if n != 'em'),
                      key=lambda n: (n.startswith('tr'), n))
        # try em-first and em-last; keep the smaller tree
        trs = [build_tree(combo, ['em'] + rest, budget_nodes=300000),
               build_tree(combo, rest + ['em'], budget_nodes=300000)]
        tr = min(trs, key=count_nodes)
        if tr[0] in ('FAIL', 'OVER'):
            tr = build_tree(combo, rest + ['em'])
        key = f'{ca},{cb}'
        out[key] = tr
        if tr[0] in ('FAIL', 'OVER', 'NEEDS_SPLIT', 'SAT', 'UNKNOWN'):
            fails.append((key, tr[0]))
        print(f'{key}: nodes={count_nodes(tr)} '
              f'({time.time() - t0:.0f}s)', flush=True)
    path = os.path.join(HERE, 's7_btem_trees.json')
    with open(path, 'w') as f:
        json.dump(out, f)
    print('wrote', path, len(out), 'trees;'
          f' fails={fails}; total={time.time() - t0:.0f}s')


if __name__ == '__main__':
    main()
