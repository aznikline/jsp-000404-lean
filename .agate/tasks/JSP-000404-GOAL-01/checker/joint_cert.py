"""Combined induction-step test: for each LP-feasible assignment, is
there a vertex t and a carry subset S (flank pairs toward t) such that
  (a) S is LP-feasible in the s-system (r_a+r_b>=1 for pairs in S),
  (b) the merged (s-1)-assignment (cells merged with carries from S)
      is fully int-feasible AND LP-feasible,
  (c) gains from S give cert:  sum_i 2^{k_i}(2^{g_i}-1) >= 2^{k_t}
      where g_i = auto_i + carry_i, auto_i = both flanks active.
"""
import itertools
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve
from del_lp2 import flank_pair
from merge_feas import merged_assign, full_int_ok


def joint_cert(assign, n, s, delta):
    nv = s * (s - 1)
    rows0 = base_rows(assign, n, s, delta)
    ks = [sum(max(m - 1, 0) for m in assign[v]) for v in range(s)]
    for t in range(s):
        need = 2 ** ks[t]
        # candidate carry pairs toward t
        pairs = []   # (i, x, y) in variable indices
        for i in range(s):
            if i == t:
                continue
            ga, gb = flank_pair(i, t, s)
            ma, mb = assign[i][ga], assign[i][gb]
            if ma >= 1 or mb >= 1:
                pairs.append((i, i * (s - 1) + ga, i * (s - 1) + gb))
        autos = {}
        for i in range(s):
            if i == t:
                continue
            ga, gb = flank_pair(i, t, s)
            autos[i] = 1 if (assign[i][ga] >= 1 and assign[i][gb] >= 1) else 0

        def test(subset):
            # (a) LP feasibility with carry constraints
            rows = list(rows0)
            for (_, x, y) in subset:
                rows.append(({x: Fr(-1), y: Fr(-1)}, Fr(-1)))
            if not lp_solve(rows, nv):
                return False
            # (b) merged feasibility
            carries = {i: (1 if any(p[0] == i for p in subset) else 0)
                       for i in range(s) if i != t}
            mg = merged_assign(assign, s, t, carries)
            if not full_int_ok(mg, n, s - 1):
                return False
            if not lp_solve(base_rows(mg, n, s - 1, delta),
                            (s - 1) * (s - 2)):
                return False
            # (c) cert
            inc = 0
            for i in range(s):
                if i == t:
                    continue
                car = 1 if any(p[0] == i for p in subset) else 0
                g = autos[i] + car
                inc += (2 ** ks[i]) * (2 ** g - 1)
            return inc >= need

        # quick check: t with auto cert and empty carry set
        inc0 = sum((2 ** ks[i]) * (2 ** autos[i] - 1)
                   for i in range(s) if i != t)
        if inc0 >= need:
            carries0 = {i: 0 for i in range(s) if i != t}
            mg = merged_assign(assign, s, t, carries0)
            if full_int_ok(mg, n, s - 1) and lp_solve(
                    base_rows(mg, n, s - 1, delta), (s - 1) * (s - 2)):
                return t, 'auto'

        # enumerate subsets small-to-large
        for sz in range(len(pairs) + 1):
            for sub in itertools.combinations(pairs, sz):
                if test(list(sub)):
                    return t, f'sub{sz}'
    return None, None


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
