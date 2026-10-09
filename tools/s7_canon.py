"""Canonical (quotiented) S7/S8 multiset-signature model, no-link mode.

Quotient table (verified against generated formulas, no link facts):

score-2 cases (21 for P=6, 28 for P=7) -> 7 canonical classes
  H_L : single 'hi' gap at index 0
  H_I : single 'hi' gap internal
  H_R : single 'hi' gap at last index
  M_LI: medpair containing 0 and one internal index
  M_LR: medpair = (0, last)
  M_II: medpair both internal   -> EXCLUDED LOCALLY by corridor
  M_IR: medpair containing last and one internal index

score-1 cases -> 3 canonical classes {0}, {internal}, {last}
"""
import itertools, json
import z3


def build(P):
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


def gap_sig_case(P, t_i, S, pv, kind, k):
    """(U, E) multiset facts, NO link. `kind` 'hi'|'med' with k in
    0..P-1, 'medpair' with k=(a,b) subset of 0..P-1."""
    U, E = [], []
    last = P - 1
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
    if kind == 'hi':
        if k == 0: elo(3); emin(4); emax(2)
        elif k == last: ehi(3); emax(4); emin(2)
        else: cpair(3, 4); emin(2); emax(2)
    elif kind == 'med':
        if k == 0: elo(2); emin(3); emax(2)
        elif k == last: ehi(2); emax(3); emin(2)
        else: cpair(2, 3); emin(2); emax(2)
    else:  # medpair
        a, b = k
        intern = [q for q in (a, b) if 0 < q < last]
        if 0 in (a, b): elo(2); emin(3)
        else: emin(2)
        if last in (a, b): ehi(2); emax(3)
        else: emax(2)
        m = len(intern)
        if m == 1: cpair(2, 3)
        elif m == 2:
            E.append(('big2', z3.Or(*[
                z3.And(x < y, y - x >= 2, y - x < 3, nb(S, x, y),
                       u < v, v - u >= 2, v - u < 3, nb(S, u, v),
                       z3.Or(y <= u, v <= x))
                for x in S for y in S for u in S for v in S])))
            E.append(('sml', z3.Or(*[z3.And(x < y, y - x < 2, nb(S, x, y))
                                     for x in S for y in S])))
    return U, E


# ---- canonical classes -------------------------------------------------
def canon2(P, c):
    """score-2 case index c -> canonical class name.
    cases: 0..P-1 'hi' singles, then medpairs in combinations order."""
    last = P - 1
    if c < P:
        return 'H_L' if c == 0 else ('H_R' if c == last else 'H_I')
    a, b = list(itertools.combinations(range(P), 2))[c - P]
    intern = [q for q in (a, b) if 0 < q < last]
    if 0 in (a, b):
        return 'M_LI' if last not in (a, b) else 'M_LR'
    if last in (a, b):
        return 'M_IR'
    return 'M_II'


def canon1(P, c):
    return 'L_0' if c == 0 else ('L_R' if c == P - 1 else 'L_I')


CANON2_ORDER = ['H_L', 'H_I', 'H_R', 'M_LI', 'M_LR', 'M_II', 'M_IR']
CANON1_ORDER = ['L_0', 'L_I', 'L_R']


def sig2_of_class(P, t_i, S, pv, cls):
    last = P - 1
    if cls == 'H_L': return gap_sig_case(P, t_i, S, pv, 'hi', 0)
    if cls == 'H_I': return gap_sig_case(P, t_i, S, pv, 'hi', 1)
    if cls == 'H_R': return gap_sig_case(P, t_i, S, pv, 'hi', last)
    if cls == 'M_LI': return gap_sig_case(P, t_i, S, pv, 'medpair', (0, 1))
    if cls == 'M_LR': return gap_sig_case(P, t_i, S, pv, 'medpair', (0, last))
    if cls == 'M_II': return gap_sig_case(P, t_i, S, pv, 'medpair', (1, 2))
    if cls == 'M_IR': return gap_sig_case(P, t_i, S, pv, 'medpair', (1, last))
    raise ValueError(cls)


def sig1_of_class(P, t_i, S, pv, cls):
    last = P - 1
    k = {'L_0': 0, 'L_I': 1, 'L_R': last}[cls]
    return gap_sig_case(P, t_i, S, pv, 'med', k)


def check(P, spec, combos=None, timeout=60000):
    """spec: [(row, kind)] with kind 's2'|'s1'. combos: canonical class
    tuples; default = product over CANON lists minus M_II for s2."""
    if combos is None:
        s2 = [c for c in CANON2_ORDER if c != 'M_II']
        per_row = [s2 if k == 's2' else CANON1_ORDER for (_, k) in spec]
        combos = itertools.product(*per_row)
    n_unsat, sats = 0, []
    for combo in combos:
        delta, t, d, D, p, base, trips = build(P)
        s = z3.Solver(); s.set("timeout", timeout)
        s.add(base)
        for tr in trips.values(): s.add(tr)
        for (row, kind), c in zip(spec, combo):
            S = [D(row, j) for j in range(P) if j != row]
            fn = sig2_of_class if kind == 's2' else sig1_of_class
            U, E = fn(P, t[row], S, p, c)
            s.add([e for _, e in U] + [e for _, e in E])
        if s.check() == z3.unsat: n_unsat += 1
        else: sats.append(combo)
    return n_unsat, sats


def verify_quotient(P=6):
    """Assert the claimed quotient table: generated (U,E) formulas are
    identical within each canonical class."""
    delta, t, d, D, p, base, trips = build(P)
    t_i, pv = t[0], p
    S = [D(0, j) for j in range(P) if j != 0]

    def sig2(c):
        last = P - 1
        if c < P: return gap_sig_case(P, t_i, S, pv, 'hi', c)
        a, b = list(itertools.combinations(range(P), 2))[c - P]
        return gap_sig_case(P, t_i, S, pv, 'medpair', (a, b))

    def key(UE):
        U, E = UE
        return tuple(e.sexpr() for _, e in U) + tuple(e.sexpr() for _, e in E)

    n2 = P + P * (P - 1) // 2
    groups2 = {}
    for c in range(n2):
        groups2.setdefault(key(sig2(c)), []).append((c, canon2(P, c)))
    ok = True
    for k, members in groups2.items():
        classes = {cl for _, cl in members}
        if len(classes) != 1:
            ok = False
            print('MIXED GROUP:', members)
    counts = {}
    for k, members in groups2.items():
        cl = members[0][1]
        counts[cl] = counts.get(cl, 0) + len(members)
    print(f'P={P} s2: {len(groups2)} formula-groups -> {counts}')
    groups1 = {}
    for c in range(P):
        groups1.setdefault(key(gap_sig_case(P, t_i, S, pv, 'med', c)),
                           []).append((c, canon1(P, c)))
    c1 = {}
    for k, members in groups1.items():
        c1[members[0][1]] = c1.get(members[0][1], 0) + len(members)
    print(f'P={P} s1: {len(groups1)} formula-groups -> {c1}')
    return ok


if __name__ == '__main__':
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else 'verify'
    if mode == 'verify':
        verify_quotient(6)
        verify_quotient(7)
    elif mode == 's7':
        for low, mid, name in [
            ((0, 1), 2, 'AA_s1_2'), ((0, 1), 5, 'AA_s1_5'),
            ((4, 5), 0, 'AB_s1_0'), ((4, 5), 3, 'AB_s1_3'),
        ]:
            spec = [(low[0], 's2'), (low[1], 's2'), (mid, 's1')]
            n, sats = check(6, spec)
            print(f'{name}: {n} unsat, sat/unk={sats}', flush=True)
    elif mode == 's8':
        for low, name in [((0, 1), 'AA'), ((0, 6), 'BT'), ((5, 6), 'AB')]:
            spec = [(low[0], 's2'), (low[1], 's2')]
            n, sats = check(7, spec)
            print(f'S8 {name}: {n} unsat, sat/unk={sats}', flush=True)
