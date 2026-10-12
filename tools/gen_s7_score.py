#!/usr/bin/env python3
"""Emit rowSig{1,2}_{P}_of_linearScore_{one,two} for P in {7,8} into
Jsp000404/S7ScoreLemmas.lean.  Mirrors N4Extraction's floor case-tree
proofs at 6 / 7 primitive gaps.
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def gaps(P):
    n = P - 2
    gs = ["(x0 - θ)"]
    for i in range(1, n):
        gs.append(f"(x{i} - x{i - 1})")
    gs.append(f"(θ + Real.pi - x{n - 1})")
    return gs


def fterm(g):
    return f"⌊{g} / lam⌋₊"


def or_nav(d, D):
    """wrap inner term as d-th disjunct of a D-arm Or."""
    if D == 1:
        return lambda s: s
    def wrap(s):
        if d < D - 1:
            s = f"Or.inl {s}"
        for _ in range(d):
            s = f"Or.inr ({s})"
        return s
    return wrap


def ord_and(P):
    n = P - 2
    ands = ["θ ≤ x0"] + [f"x{i - 1} ≤ x{i}" for i in range(1, n)] + \
           [f"x{n - 1} ≤ θ + Real.pi"]
    return " ∧ ".join(ands)


def hord_get(P, i):
    """hord component selector for gap i."""
    if i == 0:
        return "hord.1"
    n = P - 2
    if i < n:
        return "hord" + ".2" * i + ".1"
    return "hord" + ".2" * n


def emit(P, score):
    n, G = P - 2, P - 1
    gs = gaps(P)
    xs = " ".join(f"x{i}" for i in range(n))
    xl = ", ".join(f"x{i}" for i in range(n))
    sig = f"RowSig{score}_{P}"
    # disjunct forms
    if score == 2:
        singles = [(i,) for i in range(G)]            # floor = 3
        pairs = [(i, j) for i in range(G)
                 for j in range(i + 1, G)]            # floor = 2
        cases = [(3, s) for s in singles] + [(2, p) for p in pairs]
    else:
        cases = [(2, (i,)) for i in range(G)]
    D = len(cases)
    L = []
    L.append("set_option maxHeartbeats 1200000 in")
    L.append(f"theorem rowSig{score}_{P}_of_linearScore_"
             f"{'two' if score == 2 else 'one'} {{lam θ : ℝ}} "
             f"(hlam : 0 < lam)")
    L.append(f"    {{{xs} : ℝ}}")
    L.append(f"    (hord : {ord_and(P)})")
    L.append(f"    (hsc : linearGapScore lam θ (θ + Real.pi) "
             f"[{xl}] = {score}) :")
    L.append(f"    R2N4.{sig} lam Real.pi θ {xs} := by")
    for i, g in enumerate(gs):
        L.append(f"  have hg{i} : 0 ≤ {g} := by linarith "
                 f"[{hord_get(P, i)}]")
    terms = " + ".join(f"({fterm(g)} - 1)" for g in gs)
    L.append(f"  have hsum : ({terms}) = {score} := by")
    L.append("    have h := hsc")
    L.append("    simp only [linearGapScore, gapScore] at h")
    L.append("    omega")
    B = 3 if score == 2 else 2
    for i, g in enumerate(gs):
        L.append(f"  have b{i} : {fterm(g)} ≤ {B} := by omega")
    # `key`: big Or of floor-equalities
    def conj(spec):
        big, idxs = spec
        parts = []
        for k in range(G):
            if k in idxs:
                parts.append(f"{fterm(gs[k])} = {big}")
            else:
                parts.append(f"{fterm(gs[k])} ≤ 1")
        return " ∧ ".join(parts)
    L.append("  have key :")
    for i, spec in enumerate(cases[:-1]):
        L.append(f"      ({conj(spec)}) ∨")
    L.append(f"      ({conj(cases[-1])}) := by")
    # ---- proof tree ----
    big = 3 if score == 2 else 2

    def qcol(i):
        return 4 + 2 * i

    def pair_idx(i, j):
        return G + sum(G - 1 - t for t in range(i)) + (j - i - 1)

    def phase_b(i, j, col):
        """second `=2` at positions j..G-1, given r_i : f_i = 2."""
        pad = " " * col
        if j == G - 1:
            L.append(f"{pad}have s{j} : {fterm(gs[j])} = 2 := by omega")
            parts = ["r" + str(i) if k == i else
                     (f"s{j}" if k == j else "by omega")
                     for k in range(G)]
            L.append(f"{pad}exact " + or_nav(pair_idx(i, j), D)(
                     "⟨" + ", ".join(parts) + "⟩"))
            return
        L.append(f"{pad}by_cases s{j} : {fterm(gs[j])} = 2")
        parts = ["r" + str(i) if k == i else
                 (f"s{j}" if k == j else "by omega")
                 for k in range(G)]
        L.append(f"{pad}· exact " + or_nav(pair_idx(i, j), D)(
                 "⟨" + ", ".join(parts) + "⟩"))
        L.append(f"{pad}·")
        phase_b(i, j + 1, col + 2)

    def phase_a(i, col):
        """first `=2` at positions i.., all q's failed."""
        pad = " " * col
        if i == G - 2:
            L.append(f"{pad}have r{i} : {fterm(gs[i])} = 2 := by omega")
            phase_b(i, i + 1, col)
            return
        L.append(f"{pad}by_cases r{i} : {fterm(gs[i])} = 2")
        L.append(f"{pad}·")
        phase_b(i, i + 1, col + 2)
        L.append(f"{pad}·")
        phase_a(i + 1, col + 2)

    def tail(col):
        pad = " " * col
        if score == 1:
            L.append(f"{pad}exfalso; omega")
        else:
            phase_a(0, col)

    for i in range(G):
        pad = " " * qcol(i)
        if i == 0:
            L.append(f"{pad}by_cases q{i} : {fterm(gs[i])} = {big}")
        else:
            L.append(f"{pad[:-2]}· by_cases q{i} : "
                     f"{fterm(gs[i])} = {big}")
        parts = [f"q{i}" if k == i else "by omega" for k in range(G)]
        L.append(f"{pad}· exact " + or_nav(i, D)("⟨" + ", ".join(parts) + "⟩"))
        if i < G - 1:
            pass
        else:
            L.append(f"{pad}·")
            tail(qcol(i) + 2)
    # rewrite floors to interval conditions
    rw = []
    for i, g in enumerate(gs):
        if score == 2:
            rw.append(f"s7fl3 hlam hg{i}")
        rw.append(f"s7fl2 hlam hg{i}")
        rw.append(f"s7fl1 hlam hg{i}")
    L.append(f"  rw [{', '.join(rw)}] at key")
    L.append(f"  simpa only [R2N4.{sig}, and_assoc] using key")
    return L


HELPERS = '''
private theorem s7fl3 {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ = 3 ↔ 3 * lam ≤ g ∧ g < 4 * lam := by
  rw [Nat.floor_eq_iff (div_nonneg hg hlam.le)]
  constructor
  · rintro ⟨h1, h2⟩
    rw [le_div_iff₀ hlam] at h1; rw [div_lt_iff₀ hlam] at h2
    push_cast at h1 h2 ⊢; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ hlam]; exact_mod_cast h1
    · rw [div_lt_iff₀ hlam]; exact_mod_cast h2

private theorem s7fl2 {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ = 2 ↔ 2 * lam ≤ g ∧ g < 3 * lam := by
  rw [Nat.floor_eq_iff (div_nonneg hg hlam.le)]
  constructor
  · rintro ⟨h1, h2⟩
    rw [le_div_iff₀ hlam] at h1; rw [div_lt_iff₀ hlam] at h2
    push_cast at h1 h2 ⊢; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ hlam]; exact_mod_cast h1
    · rw [div_lt_iff₀ hlam]; exact_mod_cast h2

private theorem s7fl1 {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ ≤ 1 ↔ g < 2 * lam := by
  rw [show ⌊g / lam⌋₊ ≤ 1 ↔ ⌊g / lam⌋₊ < 2 from (Nat.lt_add_one_iff).symm,
    Nat.floor_lt (div_nonneg hg hlam.le), div_lt_iff₀ hlam]
  push_cast
  exact Iff.rfl
'''


def main():
    import sys
    ps = [int(a) for a in sys.argv[1:]] or [7, 8]
    if max(ps) <= 8:
        out = ["import Jsp000404.S7Defs",
               "import Jsp000404.IntervalPacking",
               "import Jsp000404.Deletion", "", "namespace Jsp404", ""] + \
              HELPERS.split("\n")
        for P in ps:
            out += emit(P, 2)
            out.append("")
            out += emit(P, 1)
            out.append("")
        out.append("end Jsp404")
        path = os.path.join(HERE, '..', 'Jsp000404', 'S7ScoreLemmas.lean')
        with open(path, 'w') as f:
            f.write("\n".join(out) + "\n")
        print('wrote', path, os.path.getsize(path))
        return
    # R1: one shard per family (single monolith exceeded the guarded
    # 180s/4GiB job caps); each shard imports only its family's Canon.
    for P in ps:
        out = [f"import Jsp000404.R1DefsN{P}Canon",
               "import Jsp000404.IntervalPacking",
               "import Jsp000404.Deletion", "", "namespace Jsp404", ""] + \
              HELPERS.split("\n")
        out += emit(P, 2)
        out.append("")
        out += emit(P, 1)
        out.append("")
        out.append("end Jsp404")
        path = os.path.join(HERE, '..', 'Jsp000404',
                            f'R1ScoreLemmasN{P}.lean')
        with open(path, 'w') as f:
            f.write("\n".join(out) + "\n")
        print('wrote', path, os.path.getsize(path))
    agg = "\n".join(f"import Jsp000404.R1ScoreLemmasN{P}" for P in ps)
    path = os.path.join(HERE, '..', 'Jsp000404', 'R1ScoreLemmas.lean')
    with open(path, 'w') as f:
        f.write(agg + "\n")
    print('wrote', path, os.path.getsize(path))


if __name__ == '__main__':
    main()
