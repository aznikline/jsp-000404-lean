"""S7/S8 minimal exact model per Lead spec (AIR-S7-S8-EXACT-MODEL-AND-REUSE).

P = number of non-anchor points (S7: P=6, S8: P=7).
p = 4 + delta, 0 <= delta < 1 (symbolic real).

0 <= t0 < ... < t_{P-1} <= delta          (theta order, no t0=0 assumption)
one shared undirected chord var d_ij = d_ji per pair i<j:
    t_i + 1 <= d_ij <= p - 1 + t_j
for i<j<k (up_trans / up_cap, both branches):
    (d_ij + 1 <= d_jk  and  d_ij < d_ik < d_jk)
  or
    (d_jk + 1 <= d_ij  and  d_jk < d_ik < d_ij)

Row at vertex i: its P-1 non-anchor chords {d_ij : j != i} sorted
r_0 < ... < r_{P-2} (asserted as sorted + a permutation of the chord
list, i.e. a big Or over all (P-1)! assignments).
P gaps: g_0 = r_0 - t_i, internal diffs, g_{P-1} = t_i + p - r_{P-2}.

score-2 signature: one gap in [3,4) rest <2, or two gaps in [2,3) rest<2.
score-1 signature: one gap in [2,3), rest <2.
No rowGain/facing/emission/minimality facts.
"""
import itertools, sys, time
import z3

z3.set_param("smt.random_seed", 0)


def build(P):
    delta = z3.Real('delta')
    t = [z3.Real(f't{i}') for i in range(P)]
    d = {(i, j): z3.Real(f'd{i}{j}') for i in range(P) for j in range(i + 1, P)}
    p = 4 + delta

    def D(i, j):
        return d[(min(i, j), max(i, j))]

    base = [z3.And(0 <= delta, delta < 1)]
    for i in range(P - 1):
        base.append(t[i] < t[i + 1])
    base += [0 <= t[0], t[P - 1] <= delta]
    for i in range(P):
        for j in range(i + 1, P):
            base += [t[i] + 1 <= d[(i, j)], d[(i, j)] <= p - 1 + t[j]]

    trips = {}
    for i, j, k in itertools.combinations(range(P), 3):
        trips[(i, j, k)] = z3.Or(
            z3.And(d[(i, j)] + 1 <= d[(j, k)],
                   d[(i, j)] < d[(i, k)], d[(i, k)] < d[(j, k)]),
            z3.And(d[(j, k)] + 1 <= d[(i, j)],
                   d[(j, k)] < d[(i, k)], d[(i, k)] < d[(i, j)]))
    return delta, t, d, D, p, base, trips


def row_gaps(row, P, t_i, D, p):
    """Return (constraints, gaps): sorted chord positions + P gaps."""
    chords = [D(row, j) for j in range(P) if j != row]
    n = len(chords)              # P-1 chords -> P gaps
    r = [z3.Real(f'r{row}_{k}') for k in range(n)]
    cons = [r[k] < r[k + 1] for k in range(n - 1)]
    # permutation of the full chord list
    cons.append(z3.Or(*[
        z3.And(*[r[k] == chords[perm[k]] for k in range(n)])
        for perm in itertools.permutations(range(n))]))
    gaps = [r[0] - t_i] + [r[k] - r[k - 1] for k in range(1, n)] + \
           [t_i + p - r[n - 1]]
    return cons, gaps


def sig_score2(gaps):
    P = len(gaps)
    cases = []
    for k in range(P):            # one gap in [3,4), rest < 2
        cases.append(z3.And(
            z3.And(3 <= gaps[k], gaps[k] < 4),
            *[gaps[l] < 2 for l in range(P) if l != k]))
    for a, b in itertools.combinations(range(P), 2):   # two gaps in [2,3)
        cases.append(z3.And(
            z3.And(2 <= gaps[a], gaps[a] < 3),
            z3.And(2 <= gaps[b], gaps[b] < 3),
            *[gaps[l] < 2 for l in range(P) if l != a and l != b]))
    return z3.Or(*cases)


def sig_score1(gaps):
    P = len(gaps)
    return z3.Or(*[
        z3.And(z3.And(2 <= gaps[k], gaps[k] < 3),
               *[gaps[l] < 2 for l in range(P) if l != k])
        for k in range(P)])


def check(P, low_ranks, mid_rank=None, use_trips=True, timeout=120000):
    """low_ranks: score-2 rows; mid_rank: optional score-1 row."""
    delta, t, d, D, p, base, trips = build(P)
    s = z3.Solver()
    s.set("timeout", timeout)
    s.add(base)
    if use_trips:
        for tr in trips.values():
            s.add(tr)
    for row in low_ranks:
        cons, gaps = row_gaps(row, P, t[row], D, p)
        s.add(cons + [sig_score2(gaps)])
    if mid_rank is not None:
        cons, gaps = row_gaps(mid_rank, P, t[mid_rank], D, p)
        s.add(cons + [sig_score1(gaps)])
    return s.check()


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    results = []
    if which in ('all', 's7'):
        # S7: P=6; low pairs (0,1),(0,5),(4,5); s1 row at a remaining rank
        print('=== S7 weak model (2 score-2 rows + 1 score-1 row) ===')
        for low in [(0, 1), (0, 5), (4, 5)]:
            for m in [r for r in range(6) if r not in low]:
                t0 = time.time()
                res = check(6, list(low), m)
                dt = time.time() - t0
                print(f'  low={low} s1_rank={m}: {res} ({dt:.1f}s)',
                      flush=True)
                results.append(('s7', low, m, res))
        print('--- S7 ablation: no triangle constraints ---')
        for low, m in [((0, 1), 2), ((0, 5), 3), ((4, 5), 0)]:
            res = check(6, list(low), m, use_trips=False)
            print(f'  low={low} s1_rank={m} no-trips: {res}', flush=True)
            results.append(('s7-notrips', low, m, res))
    if which in ('all', 's8'):
        # S8: P=7; low pairs (0,1),(0,6),(5,6); only the two score-2 rows
        print('=== S8 weak model (2 score-2 rows only) ===')
        for low in [(0, 1), (0, 6), (5, 6)]:
            t0 = time.time()
            res = check(7, list(low))
            dt = time.time() - t0
            print(f'  low={low}: {res} ({dt:.1f}s)', flush=True)
            results.append(('s8', low, None, res))
        print('--- S8 ablation: no triangle constraints ---')
        for low in [(0, 1), (0, 6), (5, 6)]:
            res = check(7, list(low), use_trips=False)
            print(f'  low={low} no-trips: {res}', flush=True)
            results.append(('s8-notrips', low, None, res))
    return results


if __name__ == '__main__':
    main()
