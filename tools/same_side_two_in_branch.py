"""Exact branch synthesizer for the same-side two-in (F/F) exclusion.

Research-only tool (no Lean trust root).  Normalizes lam = 1 and treats
pi = n + b with beta = b in (0,1).  All arithmetic is exact Fraction.

Model
-----
Five non-anchor rows {H,P,Q,R}; P,Q are short-first sources (F/F), R the
third source.  Chord variables (commutative):
  u = phi(H,P), v = phi(H,Q), z = phi(H,R),
  t = phi(P,Q), x = phi(P,R), y = phi(Q,R).
Theta vars: th,tp,tq,tr.  Slack var b = beta in (0,1), pi = n + b.

Common constraints (all non-strict for LP; strict refs are noted -- a
linear UNSAT certificate remains valid when re-strictified):
  0 <= b <= 1 ; thetas, phis in [0, n+b]
  th <= tp, th <= tq           (F side: theta_h < theta_{P,Q})
  u <= tp+1, v <= tq+1         (short-first chords P->H, Q->H)
  z >= tr+1, tr + n + b - z >= 1   (R not a ShortWitness to H)
  u <= v, v <= z               (ordered F pair, z above both)

Per leaf: a total Up-order on {H,P,Q,R}.  For every ordered pair a<b
  corridor:  ta+1 <= phi(a,b) <= tb + n+b - 1.
For every ordered triple a<b<c:
  transitivity betweenness of phi(a,c): either
     phi(a,b) < phi(a,c) < phi(b,c)   or   phi(b,c) < phi(a,c) < phi(a,b)
  cap:  |phi(b,c) - phi(a,b)| >= 1.
Both are disjunctive: the checker enumerates the choices.

Per source row (P,Q,R): the actual row order is the sort of its three
chord variables; with gaps g0..g3 (g0 = first - theta, g3 = theta+pi-last),
defect-2 means sum gapScore = n-2 with gapScore(g) = floor(g)-1 (>=0 iff
g>=1), and five_point_no_adjacent_big forbids linearly adjacent pairs
{g0,g1},{g1,g2},{g2,g3} both >= 1 (the wrap pair {g3,g0} is NOT covered).
The checker enumerates the independent big-gap set and floor values.
"""

from fractions import Fraction
from itertools import permutations, combinations, product
import sys

F = Fraction

VARS = ['th', 'tp', 'tq', 'tr', 'u', 'v', 'z', 't', 'x', 'y', 'b']
NV = len(VARS)
VIDX = {v: i for i, v in enumerate(VARS)}

# chord endpoint table: phi(a,b)
CHORD = {frozenset(('H', 'P')): 'u', frozenset(('H', 'Q')): 'v',
         frozenset(('H', 'R')): 'z', frozenset(('P', 'Q')): 't',
         frozenset(('P', 'R')): 'x', frozenset(('Q', 'R')): 'y'}
TH = {'H': 'th', 'P': 'tp', 'Q': 'tq', 'R': 'tr'}


def expr(**kw):
    """Linear form: coefficients at VIDX, optional `k=` constant in last slot."""
    e = [F(0)] * (NV + 1)
    for k_, val in kw.items():
        if k_ == 'k':
            e[-1] = F(val)
        else:
            e[VIDX[k_]] = F(val)
    return e


def sub(e1, e2, k=1):
    return [a - k * c for a, c in zip(e1, e2)]


# ---------------- exact LP feasibility (two-phase Fraction simplex) ------

def lp_feasible(cons):
    """cons: list of (coeff list, rhs) meaning a.x <= rhs, plus x>=0.
    Returns True/False, exactly (two-phase Fraction simplex)."""
    m = len(cons)
    n = NV
    ncol = n + 2 * m + 1
    T = []
    basis = []
    art_rows = []
    for i, (a, rhs) in enumerate(cons):
        a = list(a)
        rhs = F(rhs) - (a[-1] if len(a) > n else F(0))
        row = a[:n] + [F(0)] * (2 * m) + [rhs]
        if rhs >= 0:
            row[n + i] = F(1)            # slack is basic feasible
            basis.append(n + i)
        else:
            # flip sign: -a.x - s + w = -rhs ; artificial basic, w=-rhs>0
            for j in range(n):
                row[j] = -row[j]
            row[-1] = -row[-1]
            row[n + i] = F(-1)
            row[n + m + i] = F(1)
            basis.append(n + m + i)
            art_rows.append(i)
        T.append(row)

    def pivot(r, c):
        pr = T[r][c]
        T[r] = [v / pr for v in T[r]]
        for i in range(m):
            if i != r and T[i][c] != 0:
                f = T[i][c]
                T[i] = [v - f * w for v, w in zip(T[i], T[r])]
        basis[r] = c

    if not art_rows:
        return True
    # Phase I: maximize -sum artificials.  For a basic artificial w with
    # row `w + sum_j T[i][j] x_j = T[i][-1]`, we have
    #   -w = -T[i][-1] + sum_j T[i][j] x_j , so add T[i][j] to obj[j].
    obj = [F(0)] * (ncol - 1)
    for i in art_rows:
        for j in range(ncol - 1):
            obj[j] += T[i][j]
    while True:
        cands = [j for j in range(ncol - 1) if obj[j] > 0]
        if not cands:
            break
        c = min(cands)                      # Bland
        br, bv = -1, None
        for i in range(m):
            if T[i][c] > 0:
                ratio = T[i][-1] / T[i][c]
                if bv is None or ratio < bv or (ratio == bv and basis[i] < basis[br]):
                    br, bv = i, ratio
        if br < 0:
            break                           # unbounded (shouldn't happen)
        oc = obj[c]
        pivot(br, c)
        for j in range(ncol - 1):
            obj[j] -= oc * T[br][j]
    total = F(0)
    for i in art_rows:
        for j in range(m):
            if basis[j] == n + m + i:
                total += T[j][-1]
    return total == 0


def le(coeffs, rhs):
    return (coeffs, F(rhs))


def gt0(var, k=0):   # var >= k  ->  -var <= -k
    return le([F(-1) if j == VIDX[var] else F(0) for j in range(NV + 1)], -k)


def lp_ok(cons):
    return lp_feasible(cons)


# ---------------- common constraints ------------------------------------

def common_cons(n):
    C = []
    # 0 <= b <= 1 ; pi = n + b
    C.append(gt0('b'))
    C.append(le(expr(b=1), 1))
    # thetas in [0, beta] (htheta: theta i <= pi - n*lam = beta)
    for v in ['th', 'tp', 'tq', 'tr']:
        C.append(gt0(v))
        C.append((sub(expr(**{v: 1}), expr(b=1)), F(0)))
    # phis in [lam, pi]  (phi_ge_lam: every chord direction >= lam)
    for v in ['u', 'v', 'z', 't', 'x', 'y']:
        C.append(gt0(v, 1))
        C.append(le(sub(expr(**{v: 1}), expr(b=1)), n))
    # F side
    C.append((sub(expr(th=1), expr(tp=1)), F(0)))   # th <= tp
    C.append((sub(expr(th=1), expr(tq=1)), F(0)))   # th <= tq
    # short first
    C.append((sub(expr(u=1), expr(tp=1)), F(1)))   # u <= tp + 1
    C.append((sub(expr(v=1), expr(tq=1)), F(1)))
    # R not short to H (aggregate two-sided bound on chord z = phi(R,H))
    C.append((sub(expr(tr=1), expr(z=1)), F(-1)))  # tr - z <= -1
    # tr + pi - z >= 1  ->  z - tr - b <= n - 1
    C.append((sub(expr(z=1), expr(tr=1, b=1)), F(n - 1)))
    # ordering u <= v <= z
    C.append((sub(expr(u=1), expr(v=1)), F(0)))
    C.append((sub(expr(v=1), expr(z=1)), F(0)))
    return C


def corridor(n, a, b_):
    """a<b in Up order: ta+1 <= phi <= tb + pi - 1."""
    ph = CHORD[frozenset((a, b_))]
    return [
        (sub(expr(**{TH[a]: 1}), expr(**{ph: 1})), F(-1)),
        (sub(expr(**{ph: 1}), expr(**{TH[b_]: 1, 'b': 1})), F(n - 1)),
    ]


def between_opts(a, b_, c):
    """phi(a,c) between phi(a,b) and phi(b,c): two options (<= relaxed)."""
    ab, ac, bc = (CHORD[frozenset(p)] for p in [(a, b_), (a, c), (b_, c)])
    eab, eac, ebc = expr(**{ab: 1}), expr(**{ac: 1}), expr(**{bc: 1})
    opt1 = [(sub(eab, eac), F(0)), (sub(eac, ebc), F(0))]   # ab<=ac<=bc
    opt2 = [(sub(ebc, eac), F(0)), (sub(eac, eab), F(0))]   # bc<=ac<=ab
    return [opt1, opt2]


def cap_opts(a, b_, c, n):
    """lam <= |phi(b,c) - phi(a,b)| <= pi - lam (vertex angle < pi - lam)."""
    ab, bc = CHORD[frozenset((a, b_))], CHORD[frozenset((b_, c))]
    eab, ebc = expr(**{ab: 1}), expr(**{bc: 1})
    return [[(sub(eab, ebc), F(-1)),
             (sub(ebc, eab), F(n - 1))],   # 1 <= bc - ab <= pi-1
            [(sub(ebc, eab), F(-1)),
             (sub(eab, ebc), F(n - 1))]]   # 1 <= ab - bc <= pi-1


def leaf_leaves():
    """F/F: Up(H,P), Up(H,Q) fixed.  Split on Up(R,H) or Up(H,R)."""
    leaves = []
    # F1: R < H < {P,Q}
    leaves.append(('F1a', ['R', 'H', 'P', 'Q']))
    leaves.append(('F1b', ['R', 'H', 'Q', 'P']))
    # F2: H before all: 6 orders of P,Q,R
    for perm in permutations(['P', 'Q', 'R']):
        leaves.append(('F2-' + ''.join(perm), ['H'] + list(perm)))
    return leaves


def leaf_cons(n, order):
    """Base leaf constraints (corridors); returns also the disjunctions."""
    cons = []
    disj = []   # list of options-lists; each is a list of constraint lists
    for a, b_ in combinations(order, 2):
        cons += corridor(n, a, b_)
    for a, b_, c in combinations(order, 3):
        disj.append(between_opts(a, b_, c))
        disj.append(cap_opts(a, b_, c, n))
    return cons, disj


# ---------------- row-order / score enumeration --------------------------

ROWCHORDS = {'P': ['u', 't', 'x'],   # P->H, P->Q, P->R
             'Q': ['v', 'y', 't'],   # Q->H, Q->R, Q->P
             'R': ['z', 'x', 'y']}   # R->H, R->P, R->Q

INDEP_SETS = [[], [0], [1], [2], [3], [0, 2], [0, 3], [1, 3]]


def gap_exprs(row_vars, theta_var, n):
    """gaps for row order [A,B,D]: A-th, B-A, D-B, th+pi-D."""
    A, B, D = row_vars
    g3e = expr(**{theta_var: 1, 'b': 1}); g3e[-1] = F(n)   # th + pi
    return [
        sub(expr(**{A: 1}), expr(**{theta_var: 1})),                    # g0
        sub(expr(**{B: 1}), expr(**{A: 1})),                          # g1
        sub(expr(**{D: 1}), expr(**{B: 1})),                          # g2
        sub(g3e, expr(**{D: 1}))                                      # g3
    ]


def row_order_cons(chords, perm):
    """perm = ordering of chord names small->big: A<=B<=D."""
    A, B, D = perm
    return [(sub(expr(**{A: 1}), expr(**{B: 1})), F(0)),
            (sub(expr(**{B: 1}), expr(**{D: 1})), F(0))]


def floor_cons(ge, ki):
    """ki <= ge < ki+1, relaxed to ki <= ge <= ki+1 (sound for UNSAT)."""
    return [(sub([F(0)] * (NV + 1), ge), F(-ki)), (ge, F(ki + 1))]


def lt1_cons(ge):
    return [(ge, F(1))]


def check_row(n, row, base_cons):
    """Enumerate (row order, independent big set, floors); return the list
    of surviving (perm, bigs, floors, extra_cons) signatures."""
    surv = []
    chords = ROWCHORDS[row]
    for perm in permutations(chords):
        oc = row_order_cons(chords, perm)
        if not lp_ok(base_cons + oc):
            continue
        gaps = gap_exprs(perm, TH[row], n)
        for bigs in INDEP_SETS:
            k = len(bigs)
            for fls in partitions(n - 2 + k, k, 1):
                extra = list(oc)
                for gi, ki in zip(bigs, fls):
                    extra += floor_cons(gaps[gi], ki)
                for gi in set(range(4)) - set(bigs):
                    extra += lt1_cons(gaps[gi])
                if lp_ok(base_cons + extra):
                    surv.append((perm, bigs, fls, extra))
    return surv


def h_row_patterns(n):
    """H-row reduced pattern: reduced row [u,v] has score n-2 on gaps
    (u-th, v-u, th+pi-v); z splits the last gap r2 into s0 = z-v and
    s1 = th+pi-z with mergeGain mu >= 1, and floor(r2) = floor(s0+s1).

    The reduced row is synthetic (no no_adjacent_big): all floor subsets
    allowed.  mu>=1 links floors:
      both big k0,k1       -> floor(r2) in {k0+k1, k0+k1+1}
      s0 big k0, s1 small  -> carry iff frac(s0)+s1>=1 -> floor(r2)=k0+1
      s1 big k1, s0 small  -> floor(r2)=k1+1
      both small           -> mu=0, excluded.
    Yields (cons, desc)."""
    r2e = expr(th=1, b=1); r2e[-1] = F(n)   # th + pi = th + n + b
    g_red = [sub(expr(u=1), expr(th=1)),
             sub(expr(v=1), expr(u=1)),
             sub(r2e, expr(v=1))]
    s0 = sub(expr(z=1), expr(v=1))
    s1 = sub(r2e, expr(z=1))
    ZERO = [F(0)] * (NV + 1)
    all_sets = [sorted(c) for r in range(4) for c in combinations(range(3), r)]
    for bigs in all_sets:
        k = len(bigs)
        for fls in partitions(n - 2 + k, k, 1):
            cons = []
            kmap = {}
            for gi, ki in zip(bigs, fls):
                cons += floor_cons(g_red[gi], ki)
                kmap[gi] = ki
            for gi in set(range(3)) - set(bigs):
                cons += lt1_cons(g_red[gi])
            kr = kmap.get(2)           # floor of r2, or None if r2 small
            if kr is None:
                continue               # r2 < 1 -> mu = 0, dead
            for k0 in range(1, kr + 1):
                for k1 in range(1, kr + 1):
                    if k0 + k1 in (kr, kr - 1):   # both big, carry free
                        yield (cons + floor_cons(s0, k0) + floor_cons(s1, k1),
                               f'bb k0={k0} k1={k1} kr={kr}')
            # s0 big, s1 small, carry: floor(s0)=kr-1
            yield (cons + floor_cons(s0, kr - 1) + lt1_cons(s1)
                   + [(sub(ZERO, [a + c for a, c in zip(s0, s1)]),
                       F(-kr))],
                   f's0={kr-1} carry')
            # s1 big, s0 small, carry
            yield (cons + floor_cons(s1, kr - 1) + lt1_cons(s0)
                   + [(sub(ZERO, [a + c for a, c in zip(s0, s1)]),
                       F(-kr))],
                   f's1={kr-1} carry')


def check_joint(base_cons, survP, survQ, survR, limit=200000):
    """Test joint feasibility of surviving per-row signatures."""
    tried = 0
    for sP in survP:
        for sQ in survQ:
            for sR in survR:
                tried += 1
                if tried > limit:
                    return None, tried
                if lp_ok(base_cons + sP[3] + sQ[3] + sR[3]):
                    return (sP[:3], sQ[:3], sR[:3]), tried
    return 'UNSAT', tried


def partitions(total, k, lo=1):
    """compositions of `total` into k parts each >= lo."""
    if k == 0:
        if total == 0:
            yield ()
        return
    for i in range(lo, total + 1):
        for rest in partitions(total - i, k - 1, lo):
            yield (i,) + rest


def check_leaf(n, order, verbose=True):
    cons0 = common_cons(n) + leaf_cons(n, order)[0]
    disj = leaf_cons(n, order)[1]
    # enumerate all disjunction choices
    combos = list(product(*[range(len(d)) for d in disj]))
    results = []
    for combo in combos:
        cons = list(cons0)
        for di, ch in enumerate(combo):
            cons += disj[di][ch]
        if not lp_ok(cons):
            results.append(('linear-dead', combo))
            continue
        results.append(('alive', combo))
    return results


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    print('=== LP smoke test: origin region ===')
    print('common cons feasible:', lp_ok(common_cons(n)))
    print('=== F/F leaves ===')
    for name, order in leaf_leaves():
        cons0 = common_cons(n) + leaf_cons(n, order)[0]
        disj = leaf_cons(n, order)[1]
        print(f'--- {name} order={order}')
        for combo in product(*[range(len(d)) for d in disj]):
            cons = list(cons0)
            for di, ch in enumerate(combo):
                cons += disj[di][ch]
            if not lp_ok(cons):
                continue
            print(f'  alive combo={combo}')
            survs = {}
            for row in ['P', 'Q', 'R']:
                survs[row] = check_row(n, row, cons)
                sigs = sorted({(s[0], tuple(s[1]), s[2]) for s in survs[row]})
                print(f'    row {row}: {len(survs[row])} surviving patterns')
                for s in sigs[:10]:
                    print('      ', s)
            h_any = False
            for hcons, hdesc in h_row_patterns(n):
                if not lp_ok(cons + hcons):
                    continue
                h_any = True
                w, tried = check_joint(cons + hcons,
                                       survs['P'], survs['Q'],
                                       survs['R'], limit=20000)
                print(f'    Hpat {hdesc}: '
                      f'{"UNSAT" if w == "UNSAT" else w} ({tried})')
                if w not in ('UNSAT', None):
                    h_any = 'WITNESS'
            if not h_any:
                print('    ALL H/mu combos UNSAT -> leaf dead')
