import sys, random, math
sys.path.insert(0, '.')
random.seed(7)

def gaps_fan(pts, i):
    # projective directions i->j mod pi, sorted, cyclic gaps
    ds = []
    for j,p in enumerate(pts):
        if j == i: continue
        dx, dy = p[0]-pts[i][0], p[1]-pts[i][1]
        a = math.atan2(dy, dx) % math.pi
        ds.append(a)
    ds.sort()
    L = len(ds)
    gs = []
    for t in range(L):
        nxt = ds[(t+1) % L] if t+1 < L else ds[0] + math.pi
        gs.append(nxt - ds[t])
    return gs

def defects(pts, n, delta):
    lam = math.pi/(n+delta)
    cs = []
    ks = []
    for i in range(len(pts)):
        gs = gaps_fan(pts, i)
        cells = sum(int(g/lam - 1e-12) for g in gs)
        B = sum(1 for g in gs if g >= lam - 1e-12)
        c = B + (n - cells)
        k = cells - B
        cs.append(c); ks.append(k)
    return cs, ks, lam

def legal(pts, n, delta):
    # all triangle angles <= n*lam
    lam = math.pi/(n+delta)
    s = len(pts)
    for a in range(s):
        for b in range(s):
            for c in range(s):
                if len({a,b,c}) < 3: continue
                pa,pb,pc = pts[a],pts[b],pts[c]
                # angle at b
                v1 = (pa[0]-pb[0], pa[1]-pb[1]); v2 = (pc[0]-pb[0], pc[1]-pb[1])
                d = v1[0]*v2[0]+v1[1]*v2[1]
                n1 = math.hypot(*v1); n2 = math.hypot(*v2)
                if n1*n2 < 1e-12: continue
                ang = math.acos(max(-1,min(1,d/(n1*n2))))
                if ang > math.pi - lam + 1e-9: return False
    return True

# samplers producing legal configs: concircular with empty sector
def sample(n, delta, s):
    pts = []
    # concircular points with one empty arc
    R = 1.0
    arc = random.uniform(0.05, 0.9)*2*math.pi
    base = random.uniform(0, 2*math.pi)
    for _ in range(s):
        t = base + arc*random.random()
        pts.append((R*math.cos(t)+random.gauss(0,0.01), R*math.sin(t)+random.gauss(0,0.01)))
    return pts

stats = {}
for n in (3,4):
    for delta in (0.25, 0.75):
        big = delta >= 0.5
        for s in range(4, n+3):
            best = {}
            trials = 4000
            for _ in range(trials):
                pts = sample(n,delta,s)
                if not legal(pts,n,delta): continue
                cs,ks,lam = defects(pts,n,delta)
                nsat = sum(1 for c in cs if c <= 1)
                rest = sum(2.0**(-c) for c in cs if c > 1)
                tot = rest + nsat*0.5
                key = nsat
                if key not in best or tot > best[key][0]:
                    best[key] = (tot, sorted(cs))
            stats[(n,delta,s)] = best
for k,v in sorted(stats.items()):
    print(k, {ns:(round(t,3), cs) for ns,(t,cs) in v.items()})
