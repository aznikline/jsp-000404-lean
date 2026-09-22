import Mathlib
import Jsp000404.ChainWitness

/-!
# High-debt certificates — the `δ ≥ 1` (score ≥ 2) arithmetic layer

Companion to `DebtChain.lean`/`ChainWitness.lean`, specialised to the
high regime `W > 5/2`, where every mode-A-consistent skeleton is
expected to admit a certificate forcing `δ ≥ 1` (checker level 2,
gadget score `2·bound ≥ 2`).

## What is proved here

* `debt_residual_ge_one` — the `t = 1` instance of the unified
  residual theorem `debt_residual_ge`: a certificate
  `P - U - c·δ = C`, `K ≤ P`, `U ≤ B + u·δ` with capacity
  `c + u ≤ K - B - C` forces `δ ≥ 1`.

* `charge_cap_ge` — the arithmetic of **inequality-only** gadgets:
  a charged block `K ≤ A` nested in a cap `A + X ≤ B + u·δ` with
  `0 ≤ X` (nonnegative remainders on the cap range outside the
  charged arcs) forces `t ≤ δ` whenever `t·u ≤ K - B`.

  This single lemma covers every degenerate gadget family observed
  in the level-2 scans:

  * **pure cap** (`K = 0`): a direct angle `∠ = q_arc + Σr` with
    `q_arc ≥ n` satisfies `Σr ≤ (n - 1 - q_arc) + δ`, i.e.
    `B = n-1-q_arc < 0`, `u = 1`, giving `δ ≥ q_arc - (n-1)`.
  * **charge-cap block** (`K = 1 - q_A > 0`): a complementary angle
    `∠ = n + δ - (q_A + Σr_A) ≤ π - λ` charges `Σr_A ≥ 1 - q_A`,
    and a direct/nn cap on a *superrange* `B ⊇ A` turns that debt
    into `δ ≥ (1 - q_A) - (n - 1 - q_B)`.  This family was
    discovered by `tools/cert_high.py`: e.g. skeleton
    `(0,23,75,50)` of profile `(3,3,2,1)` has the exact
    certificate `r₂₁ ≥ 0`, `∠₂₀₁ ≤ π-λ` (cap `r₂₀+r₂₁ ≤ δ`),
    `∠₂₀₃ ≤ π-λ` (charge `r₂₀ ≥ 1`), giving `δ ≥ 1` with **no fan
    or triangle equality at all** — it is invisible to the
    fan/link gadget grammar of `tools/link_graph.py`.
  * **stacked blocks**: `K` may be a sum of disjoint charged arcs
    inside the same or several caps.

* `dyadic_two_zeros` / `dyadic_two_zeros4` — the weight-side
  counting lemma, proved for general `s`: if the dyadic weight
  `Σᵢ 2^{-dᵢ}` exceeds `1 + (s-1)/2` (at `s = 4` this is exactly
  the `5/2` threshold), then at least two entries satisfy
  `d i = 0` (two saturated vertices).  This is the profile-level
  engine of the case split "good saturated vertex vs. all-bad
  strip".

## What is *not* here

The combinatorial selection theorem

    `5/2 < W sk → SkeletonConsistent sk → ∃ g, Valid g ∧ 2 ≤ score g`

is not proved: the `Skeleton`/`Gadget` object layer lives on the
gadget lane (`Gadget.lean`, unfinished there) and the classification
of the hard two-saturated-vertex subcases is still open.
The complete lemma decomposition and status map is in
`notes/LANE_B.md`.
-/

namespace Jsp404

/-- High-regime residual theorem: the same certificate shape as
`debt_residual_ge_half` at target `t = 1` instead of `t = 1/2`.
Capacity condition: `c + u ≤ K - B - C`.  This is the arithmetic
core of `score g ≥ 2` once a gadget is produced. -/
theorem debt_residual_ge_one
    {P U C K c u B δ : ℝ}
    (hres : P - U - c * δ = C)
    (hP : K ≤ P)
    (hU : U ≤ B + u * δ)
    (hc : 0 < c + u)
    (hcap : c + u ≤ K - B - C) :
    (1 : ℝ) ≤ δ :=
  debt_residual_ge hres hP hU hc (by simpa using hcap)

/-- **Charge-cap gadget** (inequality-only certificate).

If a charged block satisfies `K ≤ A` and the cap bound
`A + X ≤ B + u·δ` holds on a superrange, with `0 ≤ X` (the
remainder variables in the cap range but outside the charge are
nonnegative — mode A's `r ≥ 0`), then `t·u ≤ K - B` forces
`t ≤ δ`.

Formally this is `debt_residual_ge` with residual form `P = U`,
i.e. the *zero* form `Σ_{g∈rng} r_g - Σ_{g∈rng} r_g = 0`:
no fan or triangle equality is consumed at all. -/
theorem charge_cap_ge
    {A X B u δ K t : ℝ}
    (hK : K ≤ A)
    (hX : 0 ≤ X)
    (hcap : A + X ≤ B + u * δ)
    (hu : 0 < u)
    (ht : t * u ≤ K - B) :
    t ≤ δ := by
  apply debt_residual_ge (P := A + X) (U := A + X) (C := 0)
      (K := K) (c := 0) (u := u) (B := B) (δ := δ) (t := t)
  · ring
  · linarith
  · simpa using hcap
  · simpa using hu
  · simpa using ht

/-- Pure-cap corollary: a direct angle with `q_arc ≥ n` alone forces
`δ ≥ t` when `t ≤ q_arc - (n-1)`.  With `K = 0`, `X` the full arc
sum (nonnegative), `B = n-1-q_arc`, `u = 1`. -/
theorem pure_cap_ge
    {X B δ t : ℝ}
    (hX : 0 ≤ X)
    (hcap : X ≤ B + δ)
    (ht : t ≤ -B) :
    t ≤ δ := by
  apply charge_cap_ge (A := 0) (X := X) (B := B) (u := 1)
      (K := 0) (δ := δ) (t := t)
  · linarith
  · exact hX
  · simpa using hcap
  · norm_num
  · simpa using ht

/-- Weight-side counting, proved for general `s`: if the dyadic
weight exceeds `1 + (s-1)/2` — at `s = 4` this is exactly the
`5/2` threshold — then at least two vertices are saturated
(`d i = 0`, i.e. `k_i = n-1`).  This is the profile-level reason
the high theorem decomposes into "a good saturated vertex exists"
plus the two-saturated strip case. -/
theorem dyadic_two_zeros {s : ℕ} (d : Fin s → ℕ)
    (h : 1 + ((s : ℝ) - 1) / 2 < ∑ i : Fin s, (2 : ℝ) ^ (-(d i : ℤ))) :
    ∃ i j : Fin s, i ≠ j ∧ d i = 0 ∧ d j = 0 := by
  by_contra hcon
  push Not at hcon
  -- rewrite each summand as (1/2)^(d i)
  have hterm : ∀ i : Fin s, (2 : ℝ) ^ (-(d i : ℤ)) = (1 / 2) ^ d i := by
    intro i
    rw [zpow_neg, zpow_natCast, ← one_div, one_div_pow]
  simp_rw [hterm] at h
  -- hcon : ∀ i j, i ≠ j → d i = 0 → d j ≠ 0 ; so at most one zero.
  have hcard : (Finset.univ.filter (fun i => d i = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    by_contra hij
    exact hcon i j hij hi hj
  -- elementwise bounds
  have hle1 : ∀ i : Fin s, (1 / 2 : ℝ) ^ d i ≤ 1 :=
    fun i => pow_le_one₀ (by norm_num) (by norm_num)
  have hle2 : ∀ i : Fin s, d i ≠ 0 → (1 / 2 : ℝ) ^ d i ≤ 1 / 2 := by
    intro i hi
    calc (1 / 2 : ℝ) ^ d i
        ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (Nat.one_le_iff_ne_zero.mpr hi)
      _ = 1 / 2 := pow_one _
  -- split the sum on the zero set
  set Z := Finset.univ.filter (fun i => d i = 0) with hZ
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => d i = 0) (fun i => (1 / 2 : ℝ) ^ d i)
  have hZsum : ∑ i ∈ Z, (1 / 2 : ℝ) ^ d i ≤ (Z.card : ℝ) := by
    calc ∑ i ∈ Z, (1 / 2 : ℝ) ^ d i
        ≤ ∑ i ∈ Z, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle1 i
      _ = (Z.card : ℝ) := by simp
  have hCsum : ∑ i ∈ Finset.univ.filter (fun i => ¬d i = 0),
      (1 / 2 : ℝ) ^ d i
      ≤ ((Finset.univ.filter (fun i => ¬d i = 0)).card : ℝ) / 2 := by
    calc ∑ i ∈ Finset.univ.filter (fun i => ¬d i = 0),
          (1 / 2 : ℝ) ^ d i
        ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬d i = 0),
            (1 / 2 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          apply hle2
          simpa using hi
      _ = ((Finset.univ.filter (fun i => ¬d i = 0)).card : ℝ) / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have hcards : (Z.card : ℝ)
      + ((Finset.univ.filter (fun i => ¬d i = 0)).card : ℝ) = s := by
    have hc2 : (Finset.univ.filter (fun i => d i = 0)).card
        + (Finset.univ.filter (fun i => ¬d i = 0)).card
        = Finset.univ.card :=
      Finset.card_filter_add_card_filter_not _
    rw [Finset.card_univ, Fintype.card_fin] at hc2
    exact_mod_cast hc2
  have hZr : (Z.card : ℝ) ≤ 1 := by exact_mod_cast hcard
  nlinarith [hsplit, hZsum, hCsum, hcards, hZr]

/-- The `s = 4` instance: at the high-regime threshold `W > 5/2`
the dyadic profile contains at least two zeros — i.e. at least two
saturated vertices — which is exactly the case split the high
selection theorem needs (good saturated vertex vs. the all-bad
strip). -/
theorem dyadic_two_zeros4 (d : Fin 4 → ℕ)
    (h : (5 : ℝ) / 2 < ∑ i : Fin 4, (2 : ℝ) ^ (-(d i : ℤ))) :
    ∃ i j : Fin 4, i ≠ j ∧ d i = 0 ∧ d j = 0 := by
  apply dyadic_two_zeros d
  linarith

/-- A `ResidualWitness` is *high* when its capacity slack reaches
the level-2 threshold `(c+u) ≤ K - B - C`; then `δ ≥ 1` and the
gadget score `2·bound` is `≥ 2`. -/
def ResidualWitness.High (w : ResidualWitness) : Prop :=
  w.Valid ∧ w.c + w.u ≤ w.K - w.B - w.C

theorem ResidualWitness.ge_one (w : ResidualWitness)
    (h : w.High) : (1 : ℝ) ≤ w.δ :=
  debt_residual_ge_one h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.2

end Jsp404

#print axioms Jsp404.debt_residual_ge_one
#print axioms Jsp404.charge_cap_ge
#print axioms Jsp404.pure_cap_ge
#print axioms Jsp404.dyadic_two_zeros
#print axioms Jsp404.dyadic_two_zeros4
#print axioms Jsp404.ResidualWitness.ge_one
