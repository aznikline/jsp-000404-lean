#!/usr/bin/env python3
"""gadget_check.py — replay gadgets through the Lean-mirror formulas.

Reads tools/gadget_fixtures.json and, for every fixture, recomputes
*independently* of link_graph's bookkeeping:

  * residual coefficient map   coef[v,g]      (fan + link residual form)
  * delta coefficient          dco            (Lean `form.dco`)
  * constant                   con            (Lean `form.con`)
  * charge gains / K                          (Lean `chargeGain`, `K`)
  * cap ranges, B, u per kind                 (Lean `CapEntry.range/B/u`)
  * Bcap = Σ m·B,  uu = Σ m·u                 (Lean `Bcap`, `uu`)
  * cc = -dco,  CC = -con                     (Lean `cc`, `CC`)
  * bound = 0 if cc+uu ≤ 0 else (K-Bcap-CC)/(cc+uu)   (Lean `bound`)
  * score = 2·bound                           (checker `M`)

and verifies every `Valid` side condition:

  * fans v ∈ {-1,0,1}
  * link (a,b,h,σ): σ=±1, a≠b, a≠h, b≠h
  * charge (v,a,b): a≠b, complementary, arc nonempty, coef>0 on arc
  * charges pairwise: different vertex or disjoint arcs
  * caps: m>0; piLam ⇒ a≠b ∧ direct; nn ⇒ a≠b ∧ complementary
  * coverage: -coef ≤ Σ m over caps whose range contains (v,g)
  * 0 < cc + uu

Exit code 0 iff every fixture recomputes to the stored values and all
side conditions hold.

Usage:  python3 gadget_check.py [gadget_fixtures.json]
"""
import sys, json
from fractions import Fraction as F

sys.path.insert(0, '.')


def rebuild(fx):
    """Return dict of recomputed fields + list of validity failures."""
    skel = fx['skel']
    n, s = skel['n'], skel['s']
    vtx = skel['vertices']
    errs = []

    def pos(v, u):
        return vtx[v]['pos'][str(u)]

    def bits(v, u):
        return vtx[v]['bits'][str(u)]

    def arc(v, a, b):
        lo, hi = sorted((pos(v, a), pos(v, b)))
        return list(range(lo, hi))

    def arcQ(v, a, b):
        return sum(vtx[v]['q'][g] for g in arc(v, a, b))

    def comp(v, a, b):
        return bits(v, a) != bits(v, b)

    # ---- residual form: fans then links (order irrelevant) ----
    R = {}
    dco = 0
    con = 0
    fans = {int(v): int(w) for v, w in fx['fans'].items()}
    for v, w in fans.items():
        if w not in (-1, 0, 1):
            errs.append(f'fan weight {w} not in {{-1,0,1}}')
        for g in range(s - 1):
            R[(v, g)] = R.get((v, g), 0) + w
        dco += -w
        con += w * (sum(vtx[v]['q']) - n)
    for l in fx['links']:
        a, b, h, sig = l
        if sig not in (1, -1):
            errs.append(f'link sigma {sig} not ±1')
        if not (a != b and a != h and b != h):
            errs.append(f'link {l} has repeated vertices')
        con += sig * (-n)
        dco += sig * (-1)
        for x, u, w in ((a, b, h), (b, a, h), (h, a, b)):
            qq = arcQ(x, u, w)
            if comp(x, u, w):
                con += sig * (n - qq)
                dco += sig
                for g in arc(x, u, w):
                    R[(x, g)] = R.get((x, g), 0) - sig
            else:
                con += sig * qq
                for g in arc(x, u, w):
                    R[(x, g)] = R.get((x, g), 0) + sig
    coef = {f'{v},{g}': t for (v, g), t in sorted(R.items()) if t != 0}
    cc = -dco
    CC = -con

    # ---- charges: gain = min_arc coef * (1 - q_arc) ----
    K = ZERO_ = F(0)
    for ch in fx['charges']:
        v, a, b = ch['v'], ch['a'], ch['b']
        if a == b:
            errs.append(f'charge {ch} has a=b')
            continue
        if not comp(v, a, b):
            errs.append(f'charge {ch} angle not complementary')
        ar = arc(v, a, b)
        if not ar:
            errs.append(f'charge {ch} empty arc')
        for g in ar:
            if R.get((v, g), 0) <= 0:
                errs.append(f'charge {ch} nonpositive coef at g={g}')
        gain = (min(R.get((v, g), 0) for g in ar) * (1 - arcQ(v, a, b))
                if ar else 0)
        if F(ch['gain']) != gain:
            errs.append(f'charge {ch} gain {ch["gain"]} != {gain}')
        K += gain
    for i, e in enumerate(fx['charges']):
        for e2 in fx['charges'][i + 1:]:
            if e['v'] == e2['v']:
                if set(arc(e['v'], e['a'], e['b'])) & \
                        set(arc(e2['v'], e2['a'], e2['b'])):
                    errs.append(f'charges {e} / {e2} overlap at same '
                                f'vertex')

    # ---- caps ----
    Bcap = F(0)
    uu = F(0)
    ranges = []
    for e in fx['caps']:
        v = e['v']
        if e['m'] <= 0:
            errs.append(f'cap {e} has m <= 0')
        if e['kind'] == 'rle':
            rng = [e['gap']]
            B, u = F(1), F(0)
        elif e['kind'] == 'piLam':
            if not (e['a'] != e['b'] and not comp(v, e['a'], e['b'])):
                errs.append(f'piLam cap {e} malformed')
            rng = arc(v, e['a'], e['b'])
            B, u = F(n - 1 - arcQ(v, e['a'], e['b'])), F(1)
        elif e['kind'] == 'nn':
            if not (e['a'] != e['b'] and comp(v, e['a'], e['b'])):
                errs.append(f'nn cap {e} malformed')
            rng = arc(v, e['a'], e['b'])
            B, u = F(n - arcQ(v, e['a'], e['b'])), F(1)
        else:
            errs.append(f'cap {e} bad kind')
            continue
        ranges.append((v, rng, e['m']))
        Bcap += e['m'] * B
        uu += e['m'] * u

    # ---- coverage of negative coefficients ----
    for (v, g), k in R.items():
        if k < 0:
            cov = sum(m for (vv, rng, m) in ranges
                      if vv == v and g in rng)
            if -k > cov:
                errs.append(f'coef ({v},{g})={k} undercovered: '
                            f'coverage {cov}')
    if not (cc + uu > 0):
        errs.append(f'cc+uu = {cc + uu} not positive')

    bound = F(0) if cc + uu <= 0 else (K - Bcap - CC) / (cc + uu)
    return {'coef': coef, 'dco': dco, 'con': con,
            'c': F(cc), 'u': uu, 'C': F(CC), 'K': F(K), 'Bcap': Bcap,
            'bound': bound, 'score': 2 * bound}, errs


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else 'gadget_fixtures.json'
    fxs = json.load(open(path))
    ok = bad = 0
    for fx in fxs:
        got, errs = rebuild(fx)
        checks = [
            ('coef', got['coef'], fx['coef']),
            ('dco', got['dco'], -F(fx['c'])),
            ('con', got['con'], -F(fx['C'])),
            ('c', got['c'], F(fx['c'])),
            ('u', got['u'], F(fx['u'])),
            ('C', got['C'], F(fx['C'])),
            ('K', got['K'], F(fx['K'])),
            ('Bcap', got['Bcap'], F(fx['Bcap'])),
            ('bound', got['bound'], F(fx['bound'])),
            ('score', got['score'], F(fx['score'])),
        ]
        for name, gv, xv in checks:
            if gv != xv:
                errs.append(f'{name}: recomputed {gv} != fixture {xv}')
        if errs:
            bad += 1
            print(f'{fx.get("id","?")} [{fx["skeleton"]}] FAIL')
            for e in errs:
                print(f'    {e}')
        else:
            ok += 1
            print(f'{fx.get("id","?")} [{fx["skeleton"]}] OK  '
                  f'bound={fx["bound"]} score={fx["score"]} '
                  f'tags={fx["tags"]}')
    print(f'{ok} ok, {bad} bad')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
