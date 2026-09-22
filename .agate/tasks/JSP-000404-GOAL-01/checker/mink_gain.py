"""Probe gain structure: (a) every vertex emits >=1 weighted gain?
(b) exists t with sum_i 2^{k_i}(2^{g_it}-1) >= 2^{k_t}?
(c) does the max-gap vertex always satisfy the cert?
"""
import math, random


def fan_data(pts, lam, i):
    dirs = []
    xi, yi = pts[i]
    for j, (xj, yj) in enumerate(pts):
        if j == i:
            continue
        d = math.atan2(yj - yi, xj - xi) % math.pi
        dirs.append((d, j))
    dirs.sort()
    s = len(pts)
    gaps = []
    for k in range(s - 1):
        g = dirs[(k + 1) % (s - 1)][0] - dirs[k][0]
        if k == s - 2:
            g += math.pi
        gaps.append(g)
    cells = [int(g / lam) for g in gaps]
    exp = sum(max(m - 1, 0) for m in cells)
    return dirs, gaps, cells, exp


def gain_toward(pts, lam, i, t):
    dirs, gaps, cells, _ = fan_data(pts, lam, i)
    s = len(pts)
    pos = next(k for k, (_, j) in enumerate(dirs) if j == t)
    a = (pos - 1) % (s - 1)
    b = pos % (s - 1)
    m_new = int((gaps[a] + gaps[b]) / lam)
    return max(m_new - 1, 0) - max(cells[a] - 1, 0) - max(cells[b] - 1, 0)


def main():
    random.seed(7)
    lam = 2 * math.pi / 9.0
    stat = {'emissions0': 0, 'avg_cert_fail': 0, 'maxgap_fail': 0, 'configs': 0}
    for trial in range(4000):
        s = random.choice([4, 5, 6, 7])
        pts = []
        for _ in range(s):
            a = random.uniform(0, 2 * math.pi)
            r = random.uniform(0.5, 1.5)
            pts.append((r * math.cos(a), r * math.sin(a)))
        ks = []
        maxgap = []
        for i in range(s):
            dirs, gaps, cells, e = fan_data(pts, lam, i)
            ks.append(e)
            maxgap.append(max(gaps))
        stat['configs'] += 1
        G = [[0] * s for _ in range(s)]
        for i in range(s):
            for t in range(s):
                if i != t:
                    G[i][t] = gain_toward(pts, lam, i, t)
        for i in range(s):
            E = sum((2 ** G[i][t] - 1) for t in range(s) if t != i)
            if E < 1:
                stat['emissions0'] += 1
        ok = False
        for t in range(s):
            inc = sum((2 ** ks[i]) * (2 ** G[i][t] - 1)
                      for i in range(s) if i != t)
            if inc >= 2 ** ks[t]:
                ok = True
        if not ok:
            stat['avg_cert_fail'] += 1
        t = max(range(s), key=lambda i: maxgap[i])
        inc = sum((2 ** ks[i]) * (2 ** G[i][t] - 1)
                  for i in range(s) if i != t)
        if inc < 2 ** ks[t]:
            stat['maxgap_fail'] += 1
    print(stat)


main()
