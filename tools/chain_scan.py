#!/usr/bin/env python3
# tools/chain_scan.py — offline structural scan for signed-chain
# certificates, matching the hypothesis shape of
# `signed_chain_cert` / `signed_chain_extend` in
# Jsp000404/K3bGeometry.lean.
#
# Skeleton-driven detection: every fan equality, triangle relation
# and angle bound exists in ORIG for every index, so a chain is
# certified iff the skeleton's order/bits/qs satisfy the theorem's
# hypotheses — independent of which constraints the saved LP
# certificate happened to use.  (A detected prefix chain whose
# multiplier support is absent from the saved record is still a
# valid conditional certificate.)
#
# Per candidate chain x_0..x_{L+1} (consecutive segment of
# order[x_0] starting at position p, length L+1, L >= 2):
#   * cyclic partition x_0, x_{L-1}, x_{L+1} at row x_L
#     (S_L + D_L + H_L = pi);
#   * orientation bits: same bits[i][u] == bits[i][v] iff the angle
#     at apex i with arms {u,v} is the arc branch (toReal >= 0);
#     differing bits iff the complement branch (toReal < 0) —
#     matching hbA/hbT/hbS/hbD;
#   * hsplit: x_{j-1} on the forward arc x_0 -> x_{j+1} at x_j
#     (j = 2..L-1);
#   * boundary budgets a = sum qs[x_0] over the complement of the
#     chain segment, b = sum qs[x_L] over the wrap arc x_{L+1}->x_0;
#   * score sigma = a + b + L - 2n, threshold sigma >= 2*tau.
#
# Extension: a chain of length L+1 extending a detected length-L
# chain at the same (i0, p) — the added triangle is
# Delta(x_0, x_L, x_{L+1}), the added demand is at apex x_{L+1}
# with arms {x_L, x_{L+2}}, and the ledger is
#   a' = a - q   (q = qs of the absorbed gap x_{L+1} -> x_{L+2})
#   b' = sum qs[x_{L+1}] over the new wrap x_{L+2} -> x_0
#   sigma' - sigma = 1 + (a' + b') - (a + b) = 1 + b' - b - q.
#
# usage: python tools/chain_scan.py <certs_dir> [...]

import json
import sys
import glob
from fractions import Fraction


def bits_of(row, u):
    return row["bits"].get(str(u), row["bits"].get(u))


def on_forward_arc(order, a, b, c):
    """b on the forward arc a -> c (cyclic positions)."""
    n = len(order)
    return (order.index(b) - order.index(a)) % n <= (
        order.index(c) - order.index(a)) % n


def check_chain(d, i0, p, L):
    """Validate the chain x_0..x_{L+1} at (i0, p, L) against the
    skeleton data.  Return a result dict or None."""
    n, s = d["n"], d["s"]
    skel = {e["v"]: e for e in d["skeleton"]}
    oi0 = skel[i0]["order"]
    ln = len(oi0)
    if L > ln - 1:
        return None
    x = [i0] + [oi0[(p + j) % ln] for j in range(L + 1)]
    if len(set(x)) != L + 2:
        return None
    iL = x[L]
    xLm1, xLp1 = x[L - 1], x[L + 1]

    def bit(v, u):
        return bits_of(skel[v], u)

    # cyclic partition at iL: x_0 -> x_{L-1} -> x_{L+1} -> x_0
    oiL = skel[iL]["order"]
    if not all(v in oiL for v in (i0, xLm1, xLp1)):
        return None
    if not (on_forward_arc(oiL, i0, xLm1, xLp1)
            and on_forward_arc(oiL, xLm1, xLp1, i0)
            and on_forward_arc(oiL, xLp1, i0, xLm1)):
        return None
    # orientation bits
    for j in range(1, L):
        if bit(i0, x[j]) != bit(i0, x[j + 1]):        # hbA
            return None
        if bit(x[j], i0) == bit(x[j], x[j + 1]):      # hbT
            return None
        if bit(x[j + 1], i0) != bit(x[j + 1], x[j]):  # hbS
            return None
    for j in range(1, L + 1):
        if bit(x[j], x[j - 1]) == bit(x[j], x[j + 1]):  # hbD
            return None
    # hsplit: x_{j-1} on forward arc x_0 -> x_{j+1} at x_j
    for j in range(2, L):
        if not on_forward_arc(skel[x[j]]["order"], i0, x[j - 1],
                              x[j + 1]):
            return None
    # boundary budgets
    a = sum(skel[i0]["qs"][(p + L + t) % ln] for t in range(ln - L))
    pb = oiL.index(xLp1)
    pe = oiL.index(i0)
    b = sum(skel[iL]["qs"][(pb + t) % len(oiL)]
            for t in range((pe - pb) % len(oiL)))
    sigma = a + b + L - 2 * n
    tau = Fraction(str(d["target_tau"]))
    return {"i0": i0, "iL": iL, "p": p, "L": L, "chain": x,
            "a": a, "b": b, "sigma": sigma,
            "met": Fraction(sigma) >= 2 * tau}


def detect(d):
    """All valid signed chains in the skeleton of one leaf record."""
    s = d["s"]
    out = []
    for i0 in range(s):
        ln = len(d["skeleton"][i0]["order"])
        for p in range(ln):
            for L in range(2, ln):
                ch = check_chain(d, i0, p, L)
                if ch:
                    out.append(ch)
    return out


def extension_ledger(d, ch):
    """If the detected chain has a valid one-piece extension (the
    chain at (i0, p, L+1) also validates), return the budget ledger:
    q = cells of the absorbed gap x_{L+1}->x_{L+2}, a' = a - q,
    b' = new wrap budget at x_{L+1}, dsigma = 1 + b' - b - q."""
    n = d["n"]
    skel = {e["v"]: e for e in d["skeleton"]}
    ext = check_chain(d, ch["i0"], ch["p"], ch["L"] + 1)
    if not ext or ext["chain"][:ch["L"] + 2] != ch["chain"]:
        return None
    i0, p, L = ch["i0"], ch["p"], ch["L"]
    oi0 = skel[i0]["order"]
    ln = len(oi0)
    q = skel[i0]["qs"][(p + L) % ln]
    return {
        "ext_chain": ext["chain"], "q": q,
        "a2": ext["a"], "b2": ext["b"], "sigma2": ext["sigma"],
        "dsigma": ext["sigma"] - ch["sigma"],
        "formula": 1 + ext["b"] - ch["b"] - q,
        "met2": ext["met"],
    }


def main(dirs):
    n_leaf = n_chain = n_ext = 0
    for d_ in dirs:
        for f in sorted(glob.glob(f"{d_}/leaf_*.json")):
            leaf = json.load(open(f, encoding="utf-8"))
            n_leaf += 1
            for ch in detect(leaf):
                n_chain += 1
                tag = "" if ch["met"] else "  (below tau)"
                print(f"{f}: CHAIN L={ch['L']} "
                      f"chain={ch['chain']} a={ch['a']} b={ch['b']} "
                      f"sigma={ch['sigma']}{tag}")
                led = extension_ledger(leaf, ch)
                if led:
                    n_ext += 1
                    print(f"    EXTEND -> {led['ext_chain']} "
                          f"q={led['q']} a'={led['a2']} "
                          f"b'={led['b2']} "
                          f"dsigma={led['dsigma']} "
                          f"(1+b'-b-q={led['formula']}) "
                          f"met={led['met2']}")
    print(f"---\nleaves={n_leaf} chains={n_chain} "
          f"extensions={n_ext}")


if __name__ == "__main__":
    main(sys.argv[1:] or ["."])
