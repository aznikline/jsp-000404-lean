#!/usr/bin/env python3
"""Geometric emission-digraph checker for EmissionDichotomy (P4).

Samples center configurations, computes per-center sorted direction fans
(projective reps in [0,pi)), merge gains for each deleted direction, and
tests the dichotomy:

    exists arc i->v with gain>=1 and k_i >= k_v          (CertA shape)
 OR exists v with >=2 emitters at level exactly k_v-1    (CertC shape)

Also probes mechanism candidates:
  - arc count by jump (k_v - k_i) and gain
  - whether every big gap (>= lam) produces an arc to an endpoint
  - hull-vertex emission/reception statistics
"""
import math, random, sys
from fractions import Fraction

PI = math.pi

def dir_mod_pi(a, b):
    """Projective direction rep of a->b in [0, pi)."""
    t = math.atan2(b[1]-a[1], b[0]-a[0])
    t = t % PI
    return t

def tri_angle(a, b, c):
    """Angle at b in triangle abc."""
    ux, uy = a[0]-b[0], a[1]-b[1]
    vx, vy = c[0]-b[0], c[1]-b[1]
    cr = ux*vy - uy*vx
    dot = ux*vx + uy*vy
    return math.atan2(abs(cr), dot)

def legal(pts, lam):
    s = len(pts)
    for i in range(s):
        for j in range(s):
            for k in range(s):
                if i!=j and j!=k and i!=k:
                    if tri_angle(pts[i],pts[j],pts[k]) > PI - lam + 1e-9:
                        return False
    return True

def fan(pts, i):
    s = len(pts)
    return sorted(dir_mod_pi(pts[i], pts[j]) for j in range(s) if j != i)

def cyc_gaps(row):
    """Cyclic gaps of a sorted row in [0,pi) (wrap = pi - last + first)."""
    n = len(row)
    gs = []
    for t in range(n):
        a = row[t]
        b = row[t+1] if t+1 < n else row[0] + PI
        gs.append(b - a)
    return gs

def gap_score(g, lam):
    return max(0, int(math.floor(g/lam + 1e-12)) - 1)

def row_score(row, lam):
    return sum(gap_score(g, lam) for g in cyc_gaps(row))

def row_gain(row, idx, lam):
    """rowScore after erasing row[idx] (merge its two flanking gaps)."""
    n = len(row)
    gs = cyc_gaps(row)
    # gaps: gs[t] is arc row[t] -> row[t+1]. Erasing position idx merges
    # gs[idx-1] and gs[idx] into one gap.
    merged = gs[idx-1] + gs[idx]
    rest = [gs[t] for t in range(n) if t != idx-1 and t != idx]
    rest.append(merged)
    before = sum(gap_score(g, lam) for g in gs)
    after = sum(gap_score(g, lam) for g in rest)
    return after - before

def merge_gain(g1, g2, lam):
    return (gap_score(g1+g2, lam) - gap_score(g1, lam) - gap_score(g2, lam))

def analyze(pts, lam, verbose=False):
    s = len(pts)
    rows = [fan(pts, i) for i in range(s)]
    # map direction back to vertex index
    idx_of = []
    for i in range(s):
        m = {}
        for j in range(s):
            if j != i:
                m[round(dir_mod_pi(pts[i], pts[j]), 12)] = j
        idx_of.append(m)
    ks = [row_score(r, lam) for r in rows]
    # emission digraph
    arcs = []  # (i, v, gain, jump=k_v-k_i)
    for i in range(s):
        gs = cyc_gaps(rows[i])
        for t in range(s-1):
            g = merge_gain(gs[t-1], gs[t], lam)
            if g >= 1:
                v = idx_of[i][round(rows[i][t], 12)]
                arcs.append((i, v, g, ks[v]-ks[i]))
    # dichotomy
    certA = [a for a in arcs if a[3] <= 0]
    receivers = {}
    for (i,v,g,jmp) in arcs:
        if jmp == 1:
            receivers.setdefault(v, []).append(i)
    certC = {v:es for v,es in receivers.items() if len(es) >= 2}
    # big-gap endpoint emission: every gap >= lam at i should emit to
    # at least one of its two endpoint directions
    big_silent = 0
    for i in range(s):
        gs = cyc_gaps(rows[i])
        nn = len(gs)
        for t in range(nn):
            if gs[t] >= lam - 1e-9:
                # gap t is arc row[t] -> row[t+1]; endpoints are positions
                # t (left dir, flanks gs[t-1],gs[t]) and t+1 (right dir,
                # flanks gs[t],gs[t+1])
                gL = merge_gain(gs[t-1], gs[t], lam)
                gR = merge_gain(gs[t], gs[(t+1) % nn], lam)
                if gL < 1 and gR < 1:
                    big_silent += 1
    nonflat_noarc = (any(k > 0 for k in ks) and not arcs)
    return dict(ks=ks, arcs=arcs, certA=certA, certC=certC, rows=rows,
                big_silent=big_silent, nonflat_noarc=nonflat_noarc)

def hull(pts):
    """Andrew monotone chain -> hull vertex index set."""
    n = len(pts)
    order = sorted(range(n), key=lambda i: (pts[i][0], pts[i][1]))
    def cross(o,a,b):
        return ((pts[a][0]-pts[o][0])*(pts[b][1]-pts[o][1])
                - (pts[a][1]-pts[o][1])*(pts[b][0]-pts[o][0]))
    lo=[]
    for i in order:
        while len(lo)>=2 and cross(lo[-2],lo[-1],i)<=0: lo.pop()
        lo.append(i)
    up=[]
    for i in reversed(order):
        while len(up)>=2 and cross(up[-2],up[-1],i)<=0: up.pop()
        up.append(i)
    return set(lo[:-1]+up[:-1])

def draw_gon(s):
    """Regular s-gon with +-10% radial perturbation (legal when s <= u/2)."""
    return [((0.9+0.1*random.random())*math.cos(2*PI*i/s),
             (0.9+0.1*random.random())*math.sin(2*PI*i/s)) for i in range(s)]

def draw_cluster(s):
    """Nearly-collinear points along a shallow arc (deep-tail regime)."""
    return [(i*0.9, random.random()*0.05) for i in range(s)]

def draw_uniform(s):
    return [(random.uniform(-5,5), random.uniform(-5,5)) for _ in range(s)]

def draw_arc_factory(lam):
    """Cocircular points with a big empty sector: vertices near the gap
    edge see a big fan gap (nonflat) while staying cocircular-legal.
    Constraint (cocircular): no 3 consecutive points within a 2*lam arc."""
    def draw(s):
        # choose a gap sector of size g and spread the rest over 2pi - g
        g = random.uniform(0.0, min(2*PI - 2.2*lam, 0.6*2*PI))
        span = 2*PI - g
        th0 = random.uniform(0, 2*PI)
        R = 3.0
        pts = []
        # random positions on the remaining arc
        ths = sorted(random.uniform(0, span) for _ in range(s))
        for th in ths:
            t = th0 + th
            r = R * (0.98 + 0.04*random.random())
            pts.append((r*math.cos(t), r*math.sin(t)))
        return pts
    return draw

def draw_satellite_factory(lam):
    """s-1 points on a shallow arc + one satellite beyond the arc's bulge:
    the satellite sees the cluster in a narrow fan (huge wrap gap,
    high exponent); arc vertices see forward cones (small angles)."""
    def draw(s):
        phi = random.uniform(0.2, 1.2)          # arc span (radians)
        R = 4.0
        # arc centered at origin, bulging toward +x; satellite further +x
        pts = [(R*math.cos(-phi/2 + phi*i/(s-2)) if s>2 else R,
                R*math.sin(-phi/2 + phi*i/(s-2)) if s>2 else 0.0)
               for i in range(s-1)]
        # satellite on the convex side, distance d beyond the arc
        d = random.uniform(0.5*R, 4.0*R)
        th = random.uniform(-phi/4, phi/4)
        pts.append(((R+d)*math.cos(th), (R+d)*math.sin(th)))
        # random rotation
        a0 = random.uniform(0, 2*PI)
        ca, sa = math.cos(a0), math.sin(a0)
        return [(x*ca - y*sa, x*sa + y*ca) for (x,y) in pts]
    return draw

SAMPLERS = {'u': draw_uniform, 'g': draw_gon, 'c': draw_cluster}

def main():
    random.seed(20260703)
    n_param = int(sys.argv[1]) if len(sys.argv)>1 else 3
    delta   = float(sys.argv[2]) if len(sys.argv)>2 else 0.25
    s       = int(sys.argv[3]) if len(sys.argv)>3 else 4
    trials  = int(sys.argv[4]) if len(sys.argv)>4 else 300
    mode    = sys.argv[5] if len(sys.argv)>5 else 'ugc'
    u = 2*(n_param + delta)
    lam = 2*PI/u
    SAMPLERS['a'] = draw_arc_factory(lam)
    SAMPLERS['s'] = draw_satellite_factory(lam)
    stats = dict(ok=0, legal=0, fail=0, fail_over=0, fail_F=[],
                 over=0, certA=0, certC=0, both=0,
                 arcs=0, jump_hist={}, hull_emit=0, hull_recv=0,
                 inter_emit=0, inter_recv=0, maxF=0,
                 big_silent=0, nonflat_noarc=0)
    fails = []
    for t in range(trials*60):
        if stats['ok'] >= trials: break
        pts = SAMPLERS[random.choice(mode)](s)
        # distinct
        if min(abs(pts[i][0]-pts[j][0])+abs(pts[i][1]-pts[j][1])
               for i in range(s) for j in range(i)) < 1e-3:
            continue
        if not legal(pts, lam):
            continue
        stats['legal'] += 1
        r = analyze(pts, lam)
        ks = r['ks']
        F = sum(2**k for k in ks)
        stats['arcs'] += len(r['arcs'])
        for a in r['arcs']:
            stats['jump_hist'][a[3]] = stats['jump_hist'].get(a[3],0)+1
        hasA, hasC = bool(r['certA']), bool(r['certC'])
        if hasA: stats['certA'] += 1
        if hasC: stats['certC'] += 1
        if hasA and hasC: stats['both'] += 1
        H = hull(pts)
        for (i,v,g,jmp) in r['arcs']:
            if i in H: stats['hull_emit'] += 1
            else: stats['inter_emit'] += 1
            if v in H: stats['hull_recv'] += 1
            else: stats['inter_recv'] += 1
        cap = 2**n_param + (2**(n_param-2) if delta >= 0.5 else 0)
        over = F > cap
        if over: stats['over'] += 1
        if F > stats['maxF']: stats['maxF'] = F
        if not (hasA or hasC):
            if over:
                stats['fail_over'] += 1
                fails.append((pts, ks, r['arcs'], F))
            stats['fail'] += 1
            stats['fail_F'].append(F)
        stats['big_silent'] += r['big_silent']
        if r['nonflat_noarc']:
            stats['nonflat_noarc'] += 1
            fails.append(('NOARC', pts, ks))
        stats['ok'] += 1
    print(f"n={n_param} delta={delta} s={s} lam={lam:.4f} pi/lam={PI/lam:.4f}")
    print(f"legal configs analyzed : {stats['ok']} (of {stats['legal']} legal found)")
    print(f"dichotomy failures     : {stats['fail']}  (F>cap failures: {stats['fail_over']})")
    print(f"F>cap configs          : {stats['over']}  maxF: {stats['maxF']}  fail-F: {sorted(stats['fail_F'])[:20]}")
    print(f"certA configs          : {stats['certA']}  certC: {stats['certC']}  both: {stats['both']}")
    print(f"total arcs             : {stats['arcs']}  jump histogram: {sorted(stats['jump_hist'].items())}")
    print(f"hull emit arcs         : {stats['hull_emit']}  hull recv: {stats['hull_recv']}")
    print(f"interior emit/recv     : {stats['inter_emit']} / {stats['inter_recv']}")
    print(f"big-gap silent (no endpoint emit): {stats['big_silent']}   nonflat-no-arc: {stats['nonflat_noarc']}")
    for pts, ks, arcs in fails[:3]:
        print("FAIL", ks, arcs, pts)

if __name__ == '__main__':
    main()
