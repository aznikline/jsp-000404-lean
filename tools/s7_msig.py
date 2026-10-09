"""S7 multiset-signature model: does the weaker multiset language
(elo/ehi/emin/emax/cpair/link + corridor) still refute the residual
classes that the six-centre pair-certs cannot?

P = 6 non-anchor vertices; rows have 5 chords -> 6 gaps.
Signature positional cases:
  s2: 'hi' k in 0..5 (one gap [3,4)) + medpair (a,b) in C(6,2) ([2,3) x2)
  s1: 'med' k in 0..5 (one gap [2,3))
Corridor |d_ij - d_kl| < 4 is already implied by the shared bounds
(1 <= d <= p-1+delta < 4 + ...), so no spanB port is needed.
"""
import itertools, sys, time
import z3

P = 6

def build():
    delta = z3.Real('delta')
    t = [z3.Real(f't{i}') for i in range(P)]
    d = {(i, j): z3.Real(f'd{i}{j}') for i in range(P) for j in range(i + 1, P)}
    def D(i, j): return d[(min(i, j), max(i, j))]
    p = 4 + delta
    base = [z3.And(0 <= delta, delta < 1)]
    for i in range(P - 1): base.append(t[i] < t[i + 1])
    base += [0 <= t[0], t[P - 1] <= delta]
    for i in range(P):
        for j in range(i + 1, P):
            base += [t[i] + 1 <= d[(i, j)], d[(i, j)] <= p - 1 + t[j]]
    trips = {}
    for i, j, k in itertools.combinations(range(P), 3):
        trips[(i, j, k)] = z3.Or(
            z3.And(d[(i, j)] + 1 <= d[(j, k)], d[(i, j)] < d[(i, k)],
                   d[(i, k)] < d[(j, k)]),
            z3.And(d[(j, k)] + 1 <= d[(i, j)], d[(j, k)] < d[(i, k)],
                   d[(i, k)] < d[(i, j)]))
    return delta, t, d, D, p, base, trips


def nb(S, x, y):
    return z3.And(*[z3.Or(z <= x, y <= z) for z in S])


def s7_sig_case(t_i, S, pv, kind, k):
    """(U, E) multiset facts for a 6-gap row signature case."""
    U, E = [], []
    def elo(v):
        for x in S: U.append(('elo', x - t_i >= v))
    def ehi(v):
        for x in S: U.append(('ehi', t_i + pv - x >= v))
    def emin(v): E.append(('emin', z3.Or(*[x - t_i < v for x in S])))
    def emax(v): E.append(('emax', z3.Or(*[t_i + pv - x < v for x in S])))
    def cpair(lo, hi):
        E.append(('bigk', z3.Or(*[
            z3.And(x < y, y - x >= lo, y - x < hi, nb(S, x, y))
            for x in S for y in S])))
    def link(lo_ok, hi_ok):
        """Every chord has an adjacent chord <2 away, or is <2 from
        an allowed endpoint."""
        for x in S:
            opts = []
            for y in S:
                if y is not x:
                    opts.append(z3.And(y < x, x - y < 2, nb(S, y, x)))
                    opts.append(z3.And(x < y, y - x < 2, nb(S, x, y)))
            if lo_ok: opts.append(x - t_i < 2)
            if hi_ok: opts.append(t_i + pv - x < 2)
            E.append(('link', z3.Or(*opts)))
    if kind == 'hi':
        if k == 0:
            elo(3); emin(4); emax(2); link(False, True)
        elif k == 5:
            ehi(3); emax(4); emin(2); link(True, False)
        else:
            cpair(3, 4); emin(2); emax(2); link(True, True)
    elif kind == 'med':
        if k == 0:
            elo(2); emin(3); emax(2); link(False, True)
        elif k == 5:
            ehi(2); emax(3); emin(2); link(True, False)
        else:
            cpair(2, 3); emin(2); emax(2); link(True, True)
    else:  # medpair, k = (a, b), a < b
        a, b = k
        intern = [q for q in (a, b) if 0 < q < 5]
        if 0 in (a, b):
            elo(2); emin(3)
        else:
            emin(2)
        if 5 in (a, b):
            ehi(2); emax(3)
        else:
            emax(2)
        m = len(intern)
        if m == 1:
            cpair(2, 3)
        elif m == 2:
            E.append(('big2', z3.Or(*[
                z3.And(x < y, y - x >= 2, y - x < 3, nb(S, x, y),
                       u < v, v - u >= 2, v - u < 3, nb(S, u, v),
                       z3.Or(y <= u, v <= x))
                for x in S for y in S for u in S for v in S])))
            E.append(('sml', z3.Or(*[z3.And(x < y, y - x < 2, nb(S, x, y))
                                     for x in S for y in S])))
        # link fact only valid when no chord is trapped between two
        # big/med internal gaps: trap needs a == b-1 with a,b internal
        trapped = (b == a + 1) and (0 < a) and (b < 5)
        if not trapped:
            link(a == 0, b == 5)
    return U, E


MEDPAIR6 = list(itertools.combinations(range(6), 2))   # 15 pairs
# s2 case index: 0..5 single 'hi', 6..20 medpair
def s7_sig2_case(t_i, S, pv, c):
    if c < 6: return s7_sig_case(t_i, S, pv, 'hi', c)
    return s7_sig_case(t_i, S, pv, 'medpair', MEDPAIR6[c - 6])

def s7_sig1_case(t_i, S, pv, c):
    return s7_sig_case(t_i, S, pv, 'med', c)


def probe(name, spec, combos_fn, timeout=60000):
    """spec: [(row, kind)]; combos_fn(c) -> ((kind_of_first) ...)"""
    n_unsat, n_sat, n_unk = 0, 0, 0
    sats = []
    t0 = time.time()
    combos = combos_fn()
    for combo in combos:
        delta, t, d, D, p, base, trips = build()
        s = z3.Solver(); s.set("timeout", timeout)
        s.add(base)
        for tr in trips.values(): s.add(tr)
        for (row, kind), c in zip(spec, combo):
            S = [D(row, j) for j in range(P) if j != row]
            U, E = (s7_sig2_case if kind == 's2' else s7_sig1_case)(
                t[row], S, p, c)
            s.add([e for _, e in U] + [e for _, e in E])
        r = s.check()
        if r == z3.unsat: n_unsat += 1
        elif r == z3.sat: n_sat += 1; sats.append(combo)
        else: n_unk += 1; sats.append(combo)
    print(f'{name}: {n_unsat}/{len(combos)} unsat, {n_sat} sat, '
          f'{n_unk} unknown ({time.time()-t0:.0f}s)', flush=True)
    for c in sats[:12]: print(f'   SAT/UNK combo {c}', flush=True)
    return n_unsat, n_sat


def main():
    # Residual classes mapped onto the 6-vertex model directly.
    # low pair (ranks), s1 rank; combos = (case of row a, case of row b,
    # case of s1 row): 21 x 21 x 6 = 2646
    for low, mid, name in [
        ((0, 1), 2, 'AA_s1@2'), ((0, 1), 5, 'AA_s1@5'),
        ((4, 5), 0, 'AB_s1@0'), ((4, 5), 3, 'AB_s1@3'),
    ]:
        spec = [(low[0], 's2'), (low[1], 's2'), (mid, 's1')]
        probe(name, spec,
              lambda: [(a, b, c) for a in range(21)
                       for b in range(21) for c in range(6)])

if __name__ == '__main__':
    main()
