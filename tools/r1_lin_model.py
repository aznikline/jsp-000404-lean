"""Pure-LRA R1 boundary model: no permutation Or, no If.

fwd(a,b) in [0,s)  <=>  b-a in [0,s) or b-a in [-p, s-p)
gap_j < s   <=>  exists k: d_ik - d_ij in [0,s) U [-p, s-p)  OR  t_i+p-d_ij < s
gap_j >= s  <=>  forall k: not (d_ik - d_ij in [0,s) U [-p, s-p))  AND  t_i+p-d_ij >= s
Anchor gap (t_i -> first chord) < s  <=>  exists k: d_ik - t_i < s
                              >= s  <=>  forall k: d_ik - t_i >= s
Score-0: all P gaps < 2.
Score-1: exactly one gap in [2,3), rest < 2.
Score-2: one gap [3,4) rest<2, or two gaps [2,3) rest<2.
"""
import sys, itertools, time
sys.path.insert(0, 'tools')
import s7_model, z3
z3.set_param('smt.random_seed', 0)

def inWin(diff, s, p):
    """fwd in [0,s):  diff in [0,s) or diff+p in [0,s)."""
    return z3.Or(z3.And(0 <= diff, diff < s),
                 z3.And(-p <= diff, diff < s - p))

def notWin(diff, s, p):
    return z3.And(z3.Or(diff < 0, diff >= s),
                  z3.Or(diff < -p, diff >= s - p))

def gap_lt(row, j, s, P, t_i, D, p):
    """successor gap of chord d_rowj < s (incl. end-gap option)."""
    others = [k for k in range(P) if k != row and k != j]
    return z3.Or(*[inWin(D(row, k) - D(row, j), s, p) for k in others],
                   t_i + p - D(row, j) < s)

def gap_ge(row, j, s, P, t_i, D, p):
    others = [k for k in range(P) if k != row and k != j]
    return z3.And(*[notWin(D(row, k) - D(row, j), s, p) for k in others],
                  t_i + p - D(row, j) >= s)

def anch_lt(row, s, P, t_i, D, p):
    return z3.Or(*[D(row, k) - t_i < s for k in range(P) if k != row])

def anch_ge(row, s, P, t_i, D, p):
    return z3.And(*[D(row, k) - t_i >= s for k in range(P) if k != row])

def sig0(row, P, t_i, D, p):
    return z3.And(anch_lt(row, 2, P, t_i, D, p),
                  *[gap_lt(row, j, 2, P, t_i, D, p)
                    for j in range(P) if j != row])

def sig1(row, P, t_i, D, p):
    """exactly one of the P gaps in [2,3); rest < 2."""
    idx = ['A'] + [j for j in range(P) if j != row]
    cases = []
    for big in idx:
        conj = []
        for m in idx:
            if m == big:
                if m == 'A':
                    conj += [anch_ge(row, 2, P, t_i, D, p),
                             anch_lt(row, 3, P, t_i, D, p)]
                else:
                    conj += [gap_ge(row, m, 2, P, t_i, D, p),
                             gap_lt(row, m, 3, P, t_i, D, p)]
            else:
                if m == 'A':
                    conj.append(anch_lt(row, 2, P, t_i, D, p))
                else:
                    conj.append(gap_lt(row, m, 2, P, t_i, D, p))
        cases.append(z3.And(*conj))
    return z3.Or(*cases)

def sig2(row, P, t_i, D, p):
    idx = ['A'] + [j for j in range(P) if j != row]
    cases = []
    for big in idx:                        # one gap in [3,4), rest < 2
        conj = []
        for m in idx:
            if m == big:
                conj += [(anch_ge if m == 'A' else gap_ge)(
                            *( (row, 3, P, t_i, D, p) if m == 'A'
                               else (row, m, 3, P, t_i, D, p))),
                         (anch_lt if m == 'A' else gap_lt)(
                            *( (row, 4, P, t_i, D, p) if m == 'A'
                               else (row, m, 4, P, t_i, D, p)))]
            else:
                conj.append((anch_lt if m == 'A' else gap_lt)(
                    *((row, 2, P, t_i, D, p) if m == 'A'
                      else (row, m, 2, P, t_i, D, p))))
        cases.append(z3.And(*conj))
    for b1, b2 in itertools.combinations(idx, 2):   # two gaps in [2,3)
        conj = []
        for m in idx:
            if m in (b1, b2):
                conj += [(anch_ge if m == 'A' else gap_ge)(
                            *((row, 2, P, t_i, D, p) if m == 'A'
                              else (row, m, 2, P, t_i, D, p))),
                         (anch_lt if m == 'A' else gap_lt)(
                            *((row, 3, P, t_i, D, p) if m == 'A'
                              else (row, m, 3, P, t_i, D, p)))]
            else:
                conj.append((anch_lt if m == 'A' else gap_lt)(
                    *((row, 2, P, t_i, D, p) if m == 'A'
                      else (row, m, 2, P, t_i, D, p))))
        cases.append(z3.And(*conj))
    return z3.Or(*cases)

def check(P, a_rank, s1_ranks, timeout=60000, use_trips=True):
    delta, t, d, D, p, base, trips = s7_model.build(P)
    s = z3.Solver(); s.set('timeout', timeout)
    s.add(base)
    if use_trips:
        for tr in trips.values():
            s.add(tr)
    s1set = set(s1_ranks)
    for r in range(P):
        if r == a_rank:
            s.add(sig2(r, P, t[r], D, p))
        elif r in s1set:
            s.add(sig1(r, P, t[r], D, p))
        else:
            s.add(sig0(r, P, t[r], D, p))
    return str(s.check())

if __name__ == '__main__':
    PROFILES = [
        ('T1_P6_3all', 6, 5),
        ('T2_P6_34',   6, 4),
        ('T3_P7_333',  7, 3),
        ('T4_P8_33',   8, 2),
        ('T5_P9_3',    9, 1),
        ('T6_P10_all4', 10, 0),
    ]
    res = {}
    for name, P, k in PROFILES:
        t0 = time.time(); unsat=sat=unk=0; bad=[]
        for a in range(P):
            others = [r for r in range(P) if r != a]
            for comb in itertools.combinations(others, k):
                r = check(P, a, comb)
                if r == 'unsat': unsat += 1
                elif r == 'sat': sat += 1; bad.append(('sat',a,comb))
                else: unk += 1; bad.append(('unk',a,comb))
        res[name] = dict(unsat=unsat, sat=sat, unk=unk, bad=bad[:20])
        print(f'{name}: unsat={unsat} sat={sat} unk={unk} ({time.time()-t0:.0f}s)', flush=True)
        if bad: print('   ', bad[:8], flush=True)
    import json
    json.dump(res, open('tools/r1_scan_results.json','w'), indent=1)
