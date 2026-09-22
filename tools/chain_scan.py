#!/usr/bin/env python3
# tools/chain_scan.py — offline structural scan for signed-chain
# certificates, matching the hypothesis shape of
# `signed_chain_cert` in Jsp000404/K3bGeometry.lean.
#
# For each leaf record, rebuild the chain candidates from the saved
# constraint support (nonzero multipliers) plus the skeleton's
# order/bits/qs, and check:
#   * exactly two fan equalities used, at rows i0 (anchor) and iL;
#   * the used triangle equalities form a path {i0,x_j,x_{j+1}}
#     ending at iL = x_L;
#   * x_1..x_{L+1} consecutive in order[i0] (the A_j gaps);
#   * x_0, x_{L-1}, x_{L+1} in cyclic order at row iL (S_L+D_L+H_L);
#   * every demand angle ∠(x_{j-1},x_j,x_{j+1}) used;
#   * orientation bits match the required arc/complement branches
#     (bits[i][u]==bits[i][v] iff the angle at i is the arc branch);
#   * boundary budgets a = Σ qs over the complement of the chain
#     segment at i0, b = Σ qs over x_{L+1}→x_0 at iL;
#   * score σ = a+b+L-2n, threshold σ ≥ 2τ.
#
# For detected chains with spare vertices, the script also evaluates
# the one-piece extension Δ(i0,x_{L+1},y): computes a', b', σ' and
# reports the boundary-budget change σ'-σ = 1+(a'+b')-(a+b).
#
# Offline: no LP solver, only saved JSON records.
#
# usage: python tools/chain_scan.py <certs_dir> [...]

import json
import sys
import glob
from fractions import Fraction


def key_tuple(s):
    return tuple(int(t) for t in s.strip("()").split(","))


def cyclic_pos(order, v):
    return order.index(v)


def on_forward_arc(order, a, b, c):
    """True iff b lies on the forward arc a→c (positions mod len)."""
    n = len(order)
    pa, pb, pc = order.index(a), order.index(b), order.index(c)
    return (pb - pa) % n <= (pc - pa) % n


def bits_of(row, u):
    return row["bits"].get(str(u), row["bits"].get(u))


def detect(leaf):
    """Return list of detected chain dicts for one leaf record."""
    d = leaf
    n, s = d["n"], d["s"]
    tau = Fraction(str(d["target_tau"]))
    skel = {e["v"]: e for e in d["skeleton"]}
    fans = []
    tris = []
    angs = set()
    for c in d["constraints"]:
        m = Fraction(c["multiplier"])
        if c["kind"] == "fan" and m != 0:
            fans.append(int(c["key"]))
        elif c["kind"] == "tri" and m != 0:
            tris.append(key_tuple(c["key"]))
        elif c["kind"] == "ang" and m != 0:
            angs.add(key_tuple(c["key"]))
    out = []
    if len(fans) != 2:
        return out
    for i0, iL in (fans, fans[::-1]):
        # triangles must all be anchored at i0
        pairs = []
        ok = True
        for t in tris:
            if i0 not in t:
                ok = False
                break
            others = tuple(v for v in t if v != i0)
            if len(others) != 2:
                ok = False
                break
            pairs.append(frozenset(others))
        if not ok or not tris:
            continue
        L = len(tris) + 1
        # path structure: endpoints have degree 1, iL must be one
        deg = {}
        adj = {}
        for p in pairs:
            a_, b_ = tuple(p)
            deg[a_] = deg.get(a_, 0) + 1
            deg[b_] = deg.get(b_, 0) + 1
            adj.setdefault(a_, []).append(b_)
            adj.setdefault(b_, []).append(a_)
        ends = [v for v, dv in deg.items() if dv == 1]
        if len(ends) != 2 or iL not in ends:
            continue
        if any(dv != 2 for v, dv in deg.items() if v not in ends):
            continue
        # build path x_1 .. x_L ending at iL
        xL = iL
        x1 = ends[0] if ends[1] == iL else ends[1]
        path = [x1]
        prev, cur = None, x1
        while cur != xL:
            nxt = [v for v in adj[cur] if v != prev]
            if len(nxt) != 1:
                break
            prev, cur = cur, nxt[0]
            path.append(cur)
        if cur != xL or len(path) != L:
            continue
        x = [i0] + path
        # chain positions consecutive in order[i0]
        oi0 = skel[i0]["order"]
        ln = len(oi0)
        pos0 = {v: k for k, v in enumerate(oi0)}
        if not all(v in pos0 for v in path):
            continue
        p = pos0[x[1]]
        if any(pos0[x[j + 1]] != (p + j) % ln for j in range(L)):
            continue
        xLp1 = oi0[(p + L) % ln]
        # S_L + D_L + H_L partition at iL
        oiL = skel[iL]["order"]
        if not all(v in oiL for v in (i0, x[L - 1], xLp1)):
            continue
        if not (on_forward_arc(oiL, i0, x[L - 1], xLp1)
                and on_forward_arc(oiL, x[L - 1], xLp1, i0)
                and on_forward_arc(oiL, xLp1, i0, x[L - 1])):
            continue
        # demands: ∠(x_{j-1}, x_j, x_{j+1}) used for j = 1..L
        xx = x + [xLp1]
        dem_ok = True
        for j in range(1, L + 1):
            key = (xx[j], xx[j - 1], xx[j + 1])
            key2 = (xx[j], xx[j + 1], xx[j - 1])
            if key not in angs and key2 not in angs:
                dem_ok = False
                break
        if not dem_ok:
            continue
        # orientation bits
        def bit(v, u):
            return bits_of(skel[v], u)
        bits_ok = True
        for j in range(1, L):
            # hbA: ∠(x_j,x_0,x_{j+1}) arc at x0
            if bit(i0, xx[j]) != bit(i0, xx[j + 1]):
                bits_ok = False
            # hbT: ∠(x_0,x_j,x_{j+1}) complement at x_j
            if bit(xx[j], i0) == bit(xx[j], xx[j + 1]):
                bits_ok = False
            # hbS: ∠(x_0,x_{j+1},x_j) arc at x_{j+1}
            if bit(xx[j + 1], i0) != bit(xx[j + 1], xx[j]):
                bits_ok = False
        for j in range(1, L + 1):
            # hbD: ∠(x_{j-1},x_j,x_{j+1}) complement at x_j
            if bit(xx[j], xx[j - 1]) == bit(xx[j], xx[j + 1]):
                bits_ok = False
        if not bits_ok:
            continue
        # hsplit: x_{j-1} on forward arc x_0→x_{j+1} at x_j, j = 2..L-1
        for j in range(2, L):
            if not on_forward_arc(skel[xx[j]]["order"], i0, xx[j - 1],
                                  xx[j + 1]):
                bits_ok = False
        if not bits_ok:
            continue
        # boundary budgets
        a = sum(skel[i0]["qs"][(p + L + t) % ln] for t in range(ln - L))
        qiL = skel[iL]["order"]
        pb = qiL.index(xLp1)
        pe = qiL.index(i0)
        b = sum(skel[iL]["qs"][(pb + t) % len(qiL)]
                for t in range((pe - pb) % len(qiL)))
        sigma = a + b + L - 2 * n
        out.append({
            "i0": i0, "iL": iL, "chain": x + [xLp1], "L": L,
            "a": a, "b": b, "sigma": sigma,
            "need": 2 * tau, "met": Fraction(sigma) >= 2 * tau,
        })
    return out


def extensions(leaf, ch):
    """One-piece extension candidates: new endpoint y after x_{L+1}
    in order[i0]; check the new triangle/fan structure and compute
    the boundary budgets a', b' and score σ'."""
    d = leaf
    n, s = d["n"], d["s"]
    tau = Fraction(str(d["target_tau"]))
    skel = {e["v"]: e for e in d["skeleton"]}
    i0 = ch["i0"]
    x = ch["chain"]  # x_0 .. x_{L+1}
    L = ch["L"]
    oi0 = skel[i0]["order"]
    ln = len(oi0)
    p = oi0.index(x[1])
    used = set(x)
    res = []
    for y in range(s):
        if y in used:
            continue
        # y must be the direction right after x_{L+1} in order[i0]
        if oi0[(p + L + 1) % ln] != y:
            continue
        xLm1, xL, xLp1 = x[L - 1], x[L], x[L + 1]

        def bit(v, u):
            return bits_of(skel[v], u)

        # new triangle Δ(i0, x_{L+1}, y): hbA (arc at i0),
        # hbT (complement at x_{L+1}), hbS (arc at y)
        if bit(i0, xLp1) != bit(i0, y):
            res.append({"y": y, "ok": False, "why": "hbA bit"})
            continue
        if bit(xLp1, i0) == bit(xLp1, y):
            res.append({"y": y, "ok": False, "why": "hbT bit"})
            continue
        if bit(y, i0) != bit(y, xLp1):
            res.append({"y": y, "ok": False, "why": "hbS bit"})
            continue
        # new demand at x_{L+1}: ∠(x_L, x_{L+1}, y) complement
        if bit(xLp1, xL) == bit(xLp1, y):
            res.append({"y": y, "ok": False, "why": "hbD bit"})
            continue
        # new hsplit at x_{L+1}: x_L on forward arc x_0→y
        if not on_forward_arc(skel[xLp1]["order"], i0, xL, y):
            res.append({"y": y, "ok": False, "why": "hsplit order"})
            continue
        # new right fan at x_{L+1}: cyclic order x_0, x_L, y
        oiL2 = skel[xLp1]["order"]
        if not (on_forward_arc(oiL2, i0, xL, y)
                and on_forward_arc(oiL2, xL, y, i0)
                and on_forward_arc(oiL2, y, i0, xL)):
            res.append({"y": y, "ok": False, "why": "fanR order"})
            continue
        # boundary budgets: the gap x_{L+1}→y leaves the left boundary
        a2 = ch["a"] - skel[i0]["qs"][(p + L) % ln]
        pb2 = oiL2.index(y)
        pe2 = oiL2.index(i0)
        b2 = sum(skel[xLp1]["qs"][(pb2 + t) % len(oiL2)]
                 for t in range((pe2 - pb2) % len(oiL2)))
        sig2 = a2 + b2 + (L + 1) - 2 * n
        res.append({
            "y": y, "ok": True, "a2": a2, "b2": b2, "sigma2": sig2,
            "dsigma": sig2 - ch["sigma"],
            "met2": Fraction(sig2) >= 2 * tau,
        })
    return res


def main(dirs):
    n_leaf = n_chain = n_ext_ok = 0
    for d_ in dirs:
        for f in sorted(glob.glob(f"{d_}/leaf_*.json")):
            leaf = json.load(open(f, encoding="utf-8"))
            n_leaf += 1
            chains = detect(leaf)
            for ch in chains:
                n_chain += 1
                print(f"{f}: SIGNED_CHAIN i0={ch['i0']} "
                      f"chain={ch['chain']} L={ch['L']} "
                      f"a={ch['a']} b={ch['b']} "
                      f"sigma={ch['sigma']} need={ch['need']} "
                      f"met={ch['met']}")
                exts = extensions(leaf, ch)
                for e in exts:
                    if e["ok"]:
                        n_ext_ok += 1
                        print(f"    EXTEND +{e['y']}: "
                              f"a'={e['a2']} b'={e['b2']} "
                              f"sigma'={e['sigma2']} "
                              f"dsigma={e['dsigma']} "
                              f"met={e['met2']}")
                    else:
                        print(f"    EXTEND +{e['y']}: FAIL {e['why']}")
    print(f"---\nleaves={n_leaf} chains_detected={n_chain} "
          f"extensions_ok={n_ext_ok}")


if __name__ == "__main__":
    main(sys.argv[1:] or ["."])
