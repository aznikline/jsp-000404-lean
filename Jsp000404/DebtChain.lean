import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Debt-chain — the arbitrary-length telescoping obstruction

Pure arithmetic layer of the saturation-debt mechanism.  No
geometry, no `Section4Legality`, no absolute `n`: only reals,
equalities and nonnegativity, exactly as extracted from the
mode-A Farkas certificates (`tools/mus.py`, `tools/exact_verify.py`).

## The chain template (empirically the stable MUS topology)

A *debt chain* of length `m` consists of:

* **m link equalities** (triangle sums), each decomposable as

    `S j - D j - S (j+1) + E j = cT j`

  where `S j` is the block shared with the previous link (or the
  left endpoint), `D j` the remainder debt that angle upper bounds
  charge against, `S (j+1)` the block shared with the next link,
  `E j` the block shared with the right endpoint;
* **two endpoint equalities** (fan sums)

    `S 0 + lL - δ = cL`,   `(∑ j<m, E j) + lR - δ = cR`;

* **a collective debt bound**  `K ≤ ∑ j<m, D j`
  (produced by ≤ 2 triangle-angle upper bounds in every observed
  certificate; kept arbitrary here);

* **nonnegative leftovers** `0 ≤ lL`, `0 ≤ lR`.

The signed combination  `left + right - Σ links`  telescopes: all
shared blocks cancel pairwise, leaving

    `lL + lR + Σ D j - 2δ = cL + cR - Σ cT j`.

Charging `K ≤ Σ D j` gives `δ ≥ (K - (cL + cR - Σ cT j)) / 2`, and
the capacity condition `cL + cR - Σ cT j ≤ K - 1` yields `δ ≥ 1/2`.

In the sharper identity form the excess is a sum of three provably
nonnegative slacks — the uniform normal form observed in all 8071
boundary certificates:

    `δ - 1/2 = ((Σ D j - K) + lL + lR + (K - 1 - (cL + cR - Σ cT j))) / 2`.
-/

namespace Jsp404

open Finset

/-- The algebraic heart: a signed sum over the links telescopes.
`S j - S (j+1)` collapses to `S 0 - S m`; the `E` and `D` sums pass
through unchanged. -/
theorem debt_chain_telescopes (S D E : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, (S j - D j - S (j + 1) + E j)
      = S 0 - S m + ∑ j ∈ Finset.range m, E j
        - ∑ j ∈ Finset.range m, D j := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
          Finset.sum_range_succ]
      ring

/-- Telescoped residual: the signed combination of the two endpoint
equalities and the `m` link equalities. -/
theorem debt_chain_residual
    {m : ℕ} {S D E : ℕ → ℝ} {cT : ℕ → ℝ}
    {lL lR δ cL cR : ℝ}
    (hSm : S m = 0)
    (hL : S 0 + lL - δ = cL)
    (hR : (∑ j ∈ Finset.range m, E j) + lR - δ = cR)
    (hT : ∀ j ∈ Finset.range m,
            S j - D j - S (j + 1) + E j = cT j) :
    lL + lR + ∑ j ∈ Finset.range m, D j - 2 * δ
      = cL + cR - ∑ j ∈ Finset.range m, cT j := by
  have hsum : ∑ j ∈ Finset.range m,
                (S j - D j - S (j + 1) + E j)
              = ∑ j ∈ Finset.range m, cT j :=
    Finset.sum_congr rfl fun j hj => hT j hj
  rw [debt_chain_telescopes] at hsum
  linarith

/-- The identity form: `δ - 1/2` equals half of a sum of three
slacks — debt excess `∑ D j - K`, boundary remainders `lL + lR`,
and capacity slack `K - 1 - C`.  All three are nonnegative under
`debt_chain_ge_half`'s hypotheses, giving the uniform
`δ - 1/2 = (nonneg)/2` normal form. -/
theorem debt_chain_identity
    {m : ℕ} {S D E : ℕ → ℝ} {cT : ℕ → ℝ}
    {lL lR δ cL cR K : ℝ}
    (hSm : S m = 0)
    (hL : S 0 + lL - δ = cL)
    (hR : (∑ j ∈ Finset.range m, E j) + lR - δ = cR)
    (hT : ∀ j ∈ Finset.range m,
            S j - D j - S (j + 1) + E j = cT j) :
    δ - 1 / 2
      = ((∑ j ∈ Finset.range m, D j - K) + lL + lR
         + (K - 1 - (cL + cR - ∑ j ∈ Finset.range m, cT j))) / 2 := by
  have hres := debt_chain_residual hSm hL hR hT
  linarith

/-- Unified residual theorem.  Every observed debt certificate —
two-fan chains (`c = 2`, no caps) and one-fan chains ending in an
upper-bounded cap (`c = 1`, one cap `U ≤ u·(1+δ)`) — reduces to

    `P - U - c·δ = C`,   `K ≤ P`,   `U ≤ B + u·δ`,

where `P` collects positively-signed leftovers (charged debt plus
free nonnegative remainders) and `U` the negatively-signed cap
terms.  Combining gives `δ ≥ (K - B - C)/(c + u)`; the capacity
condition `(c+u)/2 ≤ K - B - C` yields `δ ≥ 1/2`. -/
theorem debt_residual_ge_half
    {P U C K c u B δ : ℝ}
    (hres : P - U - c * δ = C)
    (hP : K ≤ P)
    (hU : U ≤ B + u * δ)
    (hc : 0 < c + u)
    (hcap : (c + u) / 2 ≤ K - B - C) :
    (1 : ℝ) / 2 ≤ δ := by
  have e : (c + u) * δ = c * δ + u * δ := by ring
  have key : (c + u) * δ ≥ K - B - C := by rw [e]; linarith
  have h2 : (c + u) * ((1 : ℝ) / 2) ≤ (c + u) * δ := by linarith
  exact le_of_mul_le_mul_left h2 hc

/-- Threshold-parameterized residual theorem: under the same
certificate shape, `t·(c+u) ≤ K - B - C` forces `δ ≥ t`.  The
integer-level law `M = 2·bound` instantiates at `t = m/2`. -/
theorem debt_residual_ge
    {P U C K c u B δ t : ℝ}
    (hres : P - U - c * δ = C)
    (hP : K ≤ P)
    (hU : U ≤ B + u * δ)
    (hc : 0 < c + u)
    (hcap : t * (c + u) ≤ K - B - C) :
    t ≤ δ := by
  have e : (c + u) * δ = c * δ + u * δ := by ring
  have key : (c + u) * δ ≥ K - B - C := by rw [e]; linarith
  have hcap' : (c + u) * t ≤ K - B - C := by rw [mul_comm]; exact hcap
  exact le_of_mul_le_mul_left (le_trans hcap' key) hc

/-- The boundary theorem: a two-fan debt chain whose capacity slack
is nonnegative forces `δ ≥ 1/2` — the low-regime phase boundary.
Obtained by instantiating `debt_residual_ge_half` at `c = 2`,
`u = 0`, `P = lL + lR + ∑ D j`. -/
theorem debt_chain_ge_half
    {m : ℕ} {S D E : ℕ → ℝ} {cT : ℕ → ℝ}
    {lL lR δ cL cR K : ℝ}
    (hSm : S m = 0)
    (hL : S 0 + lL - δ = cL)
    (hR : (∑ j ∈ Finset.range m, E j) + lR - δ = cR)
    (hT : ∀ j ∈ Finset.range m,
            S j - D j - S (j + 1) + E j = cT j)
    (hdebt : K ≤ ∑ j ∈ Finset.range m, D j)
    (hlL : 0 ≤ lL) (hlR : 0 ≤ lR)
    (hcap : cL + cR - ∑ j ∈ Finset.range m, cT j ≤ K - 1) :
    (1 : ℝ) / 2 ≤ δ := by
  have hres := debt_chain_residual hSm hL hR hT
  apply debt_residual_ge_half
      (P := lL + lR + ∑ j ∈ Finset.range m, D j)
      (U := 0) (C := cL + cR - ∑ j ∈ Finset.range m, cT j)
      (K := K) (c := 2) (u := 0) (B := 0) (δ := δ)
  · linarith
  · linarith
  · linarith
  · norm_num
  · linarith

end Jsp404

#print axioms Jsp404.debt_chain_ge_half
