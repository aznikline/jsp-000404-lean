"""Gate 2 (cyclic convention): merge preservation of FULL feasibility.

Convention (matches weighted_lp.blocks_of): vertex i's fan directions to
j != i sit at cyclic position (j-i) mod s in {1..s-1}; gap index g in
{0..s-2} is the arc AFTER position g+1; gap s-2 is the wrap (exterior).
Deleting t merges gaps (p-2, p-1) mod (s-1) where p=(t-i)%s.
"""
import itertools
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve


def blocks_of(v, j, k, s):
    pj, pk = (j - v) % s, (k - v) % s
    lo, hi = min(pj, pk), max(pj, pk)
    return list(range(lo - 1, hi - 1))


def full_int_ok(assign, n, s):
    """ALL integer constraints incl. contiguous interior block bounds,
    triangle sums, exterior >=1, vertex budget."""
    for v in range(s):
        if sum(assign[v]) > n:
            return False
        if assign[v][s - 2] < 1:
            return False
        for a in range(s - 2):
            tot = 0
            for b in range(a, s - 2):
                tot += assign[v][b]
                if tot > n - 1:
                    return False
    for (a, b, c) in itertools.combinations(range(s), 3):
        C = 0
        for (v, j, k) in ((a, b, c), (b, a, c), (c, a, b)):
            C += sum(assign[v][g] for g in blocks_of(v, j, k, s))
        if C > n:
            return False
    return True


def merged_assign(assign, s, t, carries):
    """Merge gaps flanking dir(i->t) at each i != t (cyclic convention).
    New fan over s-1 vertices indexed by old index minus shift."""
    out = []
    for i in range(s):
        if i == t:
            continue
        # direction to t at cyclic position p in {1..s-1}
        p = (t - i) % s
        ga = (p - 2) % (s - 1)
        gb = (p - 1) % (s - 1)
        # after removing direction at position p, gaps ga,gb merge.
        # merged gap sits at index ga in the new cyclic order.
        c = carries.get(i, 0)
        m = list(assign[i])
        newg = []
        for g in range(s - 1):
            if g == ga:
                newg.append(m[ga] + m[gb] + c)
            elif g == gb:
                continue
            else:
                newg.append(m[g])
        # newg has s-2 entries but the merged entry is at position ga;
        # entries after gb shift down -- order preserved cyclically.
        out.append(tuple(newg))
    return out


def merge_preserves(assign, n, s, delta):
    res = []
    for t in range(s):
        found = False
        for bits in itertools.product([0, 1], repeat=s - 1):
            carries = {}
            idx = 0
            for i in range(s):
                if i == t:
                    continue
                carries[i] = bits[idx]
                idx += 1
            mg = merged_assign(assign, s, t, carries)
            if not full_int_ok(mg, n, s - 1):
                continue
            if lp_solve(base_rows(mg, n, s - 1, delta), (s - 1) * (s - 2)):
                found = True
                break
        res.append((t, found))
    return res


if __name__ == '__main__':
    tests = [
        ([(0, 0, 3), (0, 0, 4), (0, 3, 1), (3, 0, 1)], 4, 4, Fr(3, 4)),
        ([(0, 0, 4), (0, 0, 3), (0, 3, 1), (3, 0, 1)], 4, 4, Fr(1, 4)),
    ]
    for (a, n, s, d) in tests:
        print('assign=%s' % (a,))
        print('   merge:', merge_preserves(a, n, s, d))
