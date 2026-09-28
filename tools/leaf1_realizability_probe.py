#!/usr/bin/env python3
"""leaf1_realizability_probe.py — is the unique surviving F/F leaf
geometrically realizable by 5 actual points?

Direct point model: anchor v at origin, four successors on rays
theta_h < {theta_a, theta_b}, theta_t free, all theta in [0, beta),
beta = pi - n in (0,1) with n = 3 (lam = 1).

A point on ray theta_i at distance r_i.  Chord direction mod pi for pair
(x, y) is computed from the actual vectors.  Constraints (leaf 1):

  h-row F/F: th < phi_ha < phi_hb < phi_ht, phi_ha,phi_hb in [th+1, beta+1)
  two_in_F_above: phi_ht > phi_hb ; defect(h) = 3 (mu = 1)
  leaf-1 row orders:
    a: th_a < p_ha < p_at < p_ab
    b: th_b < p_hb < p_bt < p_ab
    t: th_t < p_at < p_bt < p_ht
  Up orientations: a->b, h->a, h->b, t->a, t->b, t->h (encoded as
  corridor-compatible: phi_xy >= theta_src + lam for chosen source)
  scores: rows a,b,t defect 2 (sum over 4 gaps of max(floor(g)-1,0) = n-2)
          row h defect 3 (sum = n-3) ; anchor defect 1.

If a feasible 5-point config exists => same_side_two_in_F_impossible is
FALSE as stated and the R=3 plan needs revision.  Report best-fit
residuals over many seeds.
"""

import numpy as np
from scipy.optimize import least_squares

N = 3
PI_RANGE = (N, N + 1)          # beta = pi - N in (0,1); lam = 1
PI = np.pi                    # actual pi used for geometry


def dirrep(p_from, p_to):
    d = p_to - p_from
    a = np.arctan2(d[1], d[0]) % np.pi
    return a


def row_score(th, phis):
    """positions = phis lifted into [th, th+pi); 4 gaps; sum max(floor-1,0)."""
    pos = sorted(p if p >= th - 1e-9 else p + np.pi for p in phis)
    gaps = [pos[0] - th, pos[1] - pos[0], pos[2] - pos[1], th + np.pi - pos[2]]
    return sum(max(int(np.floor(g - 1e-9)) - 1, 0) for g in gaps)


def unpack(u):
    th, ta, tb, tt = 0.0, u[0], u[1], u[2]
    rh, ra, rb, rt = u[3], u[4], u[5], u[6]
    return (th, ta, tb, tt), (rh, ra, rb, rt)


def points(thetas, rs):
    return {k: np.array([r * np.cos(t), r * np.sin(t)])
            for k, (t, r) in zip("habt", zip(thetas, rs))}


def residuals(u):
    (th, ta, tb, tt), rs = unpack(u)
    thetas = dict(h=th, a=ta, b=tb, t=tt)
    pts = points((th, ta, tb, tt), rs)
    phi = {}
    for x in "habt":
        for y in "habt":
            if x < y:
                phi[(x, y)] = dirrep(pts[x], pts[y])
    ph = lambda x, y: phi[tuple(sorted((x, y)))]
    res = []
    # theta constraints: 0 <= th(=0) < ta, tb ; all <= 0.95 ; tt in [0,0.95]
    res += [ta - 1e-3, tb - 1e-3, tt + 1e-3, 0.95 - ta, 0.95 - tb, 0.95 - tt]
    # positivity of distances
    res += [r - 0.05 for r in rs]
    # F windows on h's row: th+1 <= phi_ha < phi_hb < beta+1
    res += [ph('h', 'a') - 1.0, 1.95 - ph('h', 'a'),
            ph('h', 'b') - ph('h', 'a'), 1.95 - ph('h', 'b')]
    # two_in_F_above: phi_ht > phi_hb
    res += [ph('h', 't') - ph('h', 'b')]
    # leaf-1 row orders (penalize violations)
    for lhs, rhs in [
            (ph('h', 'a'), ph('a', 't')), (ph('a', 't'), ph('a', 'b')),   # row a
            (ph('h', 'b'), ph('b', 't')), (ph('b', 't'), ph('a', 'b')),   # row b
            (ph('a', 't'), ph('b', 't')), (ph('b', 't'), ph('h', 't')),   # row t
            ]:
        res.append(rhs - lhs)
    # corridor for chosen Up sources: phi >= theta_src + 1 (soft)
    for (x, y) in [('h', 'a'), ('h', 'b'), ('a', 'b'),
                   ('t', 'a'), ('t', 'b'), ('t', 'h')]:
        res.append(ph(x, y) - thetas[x] - 1.0)
    # scores (hard equalities, large weight)
    th_map = dict(h=th, a=ta, b=tb, t=tt)
    tgt = dict(h=N - 3, a=N - 2, b=N - 2, t=N - 2)
    for r in "abt" + "h":
        sc = row_score(th_map[r],
                       [ph(r, o) for o in "habt" if o != r])
        res.append(6.0 * (sc - tgt[r]))
    # anchor row: positions thetas, defect 1 -> score n-1
    ord_t = sorted([ta, tb, tt, th])
    agaps = [ord_t[0]] + [ord_t[i + 1] - ord_t[i] for i in range(3)] + \
            [np.pi - ord_t[3]]
    ascore = sum(max(int(np.floor(g - 1e-9)) - 1, 0) for g in agaps)
    res.append(6.0 * (ascore - (N - 1)))
    return np.array(res)


def main():
    rng = np.random.default_rng(0)
    best = None
    for seed in range(400):
        u0 = np.array([
            rng.uniform(0.05, 0.9), rng.uniform(0.05, 0.9),
            rng.uniform(-0.5, 0.9),
            rng.uniform(0.3, 6.0), rng.uniform(0.3, 6.0),
            rng.uniform(0.3, 6.0), rng.uniform(0.3, 6.0)])
        try:
            sol = least_squares(residuals, u0, method='lm',
                                max_nfev=2000)
        except Exception:
            continue
        cost = np.sum(residuals(sol.x) ** 2)
        neg = np.sum(np.minimum(residuals(sol.x), 0) ** 2)
        score_err = np.abs(residuals(sol.x)[-4:] / 6).sum()
        if best is None or (neg, score_err) < (best[0], best[1]):
            best = (neg, score_err, sol.x, cost)
    neg, serr, x, cost = best
    print(f"best: ineq-violation^2={neg:.4g} score-residual={serr:.4g} "
          f"total={cost:.4g}")
    print("u* =", np.round(x, 4))
    print("residuals:", np.round(residuals(x), 4))


if __name__ == "__main__":
    main()
