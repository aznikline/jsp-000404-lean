"""Lane E — geometry-driven skeleton generator (s-generic).

Real point configs produce edge-side-consistent skeletons by
construction.  Config families biased toward extreme profiles:

  collinear : points on a line + epsilon perpendicular noise
  circle    : (near-)regular polygon + jitter
  cluster   : k points tight cluster + rest spread
  two-cluster / arc-clustered variants
  random    : uniform

For every skeleton: kv profile -> deficit d -> W; LP min-delta
(float then exact on interesting hits).

Usage: python3 e_geom.py s nconf [seed]
"""
import sys, math, random, time, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le


def real_skel(P, n, lam):
    """Skeleton of point config P at modulus lam (1/(n+delta) units).
    Returns (sol, kvs) or None if side signs inconsistent."""
    s = len(P)
    V = []
    for i in range(s):
        dirs = {j: math.atan2(P[j][1] - P[i][1], P[j][0] - P[i][0])
                % math.pi for j in range(s) if j != i}
        order = sorted(dirs, key=lambda j: dirs[j])
        angs = [dirs[j] for j in order]
        m = s - 1
        gaps = [((angs[(t + 1) % m] - angs[t]) % math.pi) / math.pi
                for t in range(m)]
        qs = tuple(int(math.floor(g / lam)) for g in gaps)
        if any(q < 0 or q > n for q in qs):
            return None
        side = {}
        for j in order:
            for k in order:
                if k == j:
                    continue
                cr = ((P[j][0] - P[i][0]) * (P[k][1] - P[i][1])
                      - (P[j][1] - P[i][1]) * (P[k][0] - P[i][0]))
                side[(j, k)] = 1 if cr > 0 else -1
        pos = {d: t for t, d in enumerate(order)}
        bits = {order[0]: 0}
        b0 = order[0]
        for k in order[1:]:
            sgn = 1 if pos[k] > pos[b0] else -1
            bits[k] = 0 if side[(b0, k)] == sgn else 1
        ok = True
        for j in order:
            for k in order:
                if k == j:
                    continue
                sgn = (1 if pos[k] > pos[j] else -1) \
                    * (-1 if bits[j] != bits[k] else 1)
                if side[(j, k)] != sgn:
                    ok = False
        if not ok:
            return None
        V.append(le.mk_variant(i, tuple(order), bits, qs, n))
    return V, [sum(max(q - 1, 0) for q in v['qs']) for v in V]


def gen_config(fam, s, rng):
    if fam == 'collinear':
        x = sorted(rng.uniform(0, 10) for _ in range(s))
        return [(xx, rng.gauss(0, 0.02)) for xx in x]
    if fam == 'collinear2':  # heavier noise
        x = sorted(rng.uniform(0, 10) for _ in range(s))
        return [(xx, rng.gauss(0, 0.2)) for xx in x]
    if fam == 'circle':
        r0 = rng.uniform(3, 8)
        rot = rng.uniform(0, 2 * math.pi)
        return [(r0 * math.cos(rot + 2 * math.pi * t / s)
                 + rng.gauss(0, 0.05),
                 r0 * math.sin(rot + 2 * math.pi * t / s)
                 + rng.gauss(0, 0.05)) for t in range(s)]
    if fam == 'cluster':
        k = rng.randrange(1, s)
        cx, cy = rng.uniform(0, 10), rng.uniform(0, 10)
        pts = [(cx + rng.gauss(0, 0.05), cy + rng.gauss(0, 0.05))
               for _ in range(k)]
        pts += [(rng.uniform(0, 10), rng.uniform(0, 10))
                for _ in range(s - k)]
        return pts
    if fam == 'twoarc':     # two tight arcs on a circle
        r0 = rng.uniform(4, 8)
        a1 = rng.uniform(0, 2 * math.pi)
        a2 = a1 + rng.uniform(0.5, math.pi)
        pts = []
        for t in range(s):
            a = a1 if t < s // 2 else a2
            pts.append((r0 * math.cos(a + rng.gauss(0, 0.03)),
                        r0 * math.sin(a + rng.gauss(0, 0.03))))
        return pts
    return [(rng.uniform(0, 10), rng.uniform(0, 10))
            for _ in range(s)]


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nconf = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    n = s
    rng = random.Random(seed)
    fams = ['collinear', 'collinear2', 'circle', 'cluster',
            'twoarc', 'random']
    seen = {}
    feas = tot = 0
    t0 = time.time()
    best_rows = []
    for tr in range(nconf):
        fam = fams[tr % len(fams)]
        for dval in (0.1, 0.3, 0.5, 0.7, 0.9):
            lam = 1.0 / (n + dval)
            P = gen_config(fam, s, rng)
            out = real_skel(P, n, lam)
            tot += 1
            if out is None:
                continue
            sol, kv = out
            st, lo = le.lp_f(sol, n)
            if st != 'bounded':
                continue
            feas += 1
            d = tuple(sorted(n - 1 - k for k in kv))
            W = le.W_of_d(d)
            lof = F(lo).limit_denominator(96)
            key = (d, str(lof))
            if key not in seen:
                seen[key] = le.sol_to_data(sol)
            band = 'hi' if W > F(5, 2) else ('mid' if W > 2 else 'lo')
            viol = (band == 'hi' and lof < 1) or \
                   (band == 'mid' and lof < F(1, 2))
            row = (float(W), d, str(lof), fam, dval, viol)
            best_rows.append(row)
            if viol or (band == 'hi' and lof <= 1) \
                    or (band == 'mid' and lof <= F(1, 2)):
                print('%s%s d=%s W=%s mind=%s fam=%s dv=%.1f kv=%s'
                      % ('*** ' if viol else '', 'HIT' if viol
                         else 'row', d, str(W), str(lof), fam,
                         dval, kv), flush=True)
    print('\nfeasible %d / %d skels (%.0fs)' % (feas, tot,
                                              time.time() - t0))
    best_rows.sort(key=lambda r: (-r[0], r[2]))
    print('top rows by W (feasible):')
    for r in best_rows[:40]:
        print('   W=%.4f d=%s mind=%s fam=%s dv=%.1f %s'
              % (r[0], r[1], r[2], r[3], r[4],
                 'VIOL' if r[5] else ''))
    json.dump({'rows': [list(map(str, r)) for r in best_rows]},
              open('lane_e_geom_s%d.json' % s, 'w'), indent=1)


if __name__ == '__main__':
    main()
