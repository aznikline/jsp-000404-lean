"""n=4 six-centre scalar model (multiset row encoding).

Row signature facts are stated over the chord *multiset* of a row:
endpoint gaps give universal lower/upper bounds on all chords; internal
gaps give consecutive-pair (adjacent in sorted order) witnesses; plus a
telescoping span bound on every chord pair.  `nb(S,x,y)` is the
'no chord strictly between' adjacency conjunct.
"""
import z3, itertools

P = 5

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

def gaps_of(t_i, r, pv):
    return [r[0] - t_i, r[1] - r[0], r[2] - r[1], r[3] - r[2],
            t_i + pv - r[3]]

# -- signature cases over a chord multiset S -------------------------------
# 'hi' k     : one gap in [3,4) at position k, rest < 2   (score-2, single)
# 'medpair'(a,b) : two gaps in [2,3) at positions a,b     (score-2, pair)
# 'med' k    : one gap in [2,3) at position k, rest < 2   (score-1)
# Returns (U, E): lists of (tag, expr); U = universal facts, E = or-facts.

def sig_case(t_i, S, pv, kind, k):
    U, E = [], []
    def spanB(B):
        for x in S:
            for y in S: U.append(('sp', y - x < B))
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
        if k == 0: elo(3); spanB(6); emin(4); emax(2)
        elif k == 4: ehi(3); spanB(6); emax(4); emin(2)
        else: cpair(3, 4); spanB(8); emin(2); emax(2)
    elif kind == 'med':
        if k == 0: elo(2); spanB(6); emin(3); emax(2)
        elif k == 4: ehi(2); spanB(6); emax(3); emin(2)
        else: cpair(2, 3); spanB(7); emin(2); emax(2)
    else:  # medpair, k = (a,b)
        a, b = k
        intern = [q for q in (a, b) if q in (1, 2, 3)]
        if 0 in (a, b): elo(2); emin(3)
        else: emin(2)
        if 4 in (a, b): ehi(2); emax(3)
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
        spanB(m + 6)
    return U, E

MEDPAIR = list(itertools.combinations(range(5), 2))  # 10 index pairs

def sig2_case(t_i, S, pv, c):
    """score-2 signature case c in 0..14: 0-4 single-high, 5-14 medpair."""
    if c < 5: return sig_case(t_i, S, pv, 'hi', c)
    return sig_case(t_i, S, pv, 'medpair', MEDPAIR[c - 5])

def sig1_case(t_i, S, pv, c):
    return sig_case(t_i, S, pv, 'med', c)

# -- emission (residual sliver chord) --------------------------------------
def em_case(t, D, p, r, w):
    return D(r, w) > t[r] + p - 1 if r < w else D(r, w) < t[r] + 1
