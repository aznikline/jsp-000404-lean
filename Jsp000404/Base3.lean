import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Section-4 base case `s = 3`: the two-regime weighted bound

For a 3-center configuration the cell data consists, at each vertex
`i`, of an *exterior* gap cell count `ext i` and the exponent
`k i = Σ_g max (m_g - 1) 0`.  Three elementary consequences of the
fan/remainder system (Section 4, (4.11)–(4.13)) suffice for the full
staircase bound at `s = 3`:

* **L1** `ext_pos`: every exterior gap contains at least one cell.
* **L2** `top_requires_sat`: `k i = n - 1` forces exterior saturation
  `ext i = n`.
* **L3** `ext_budget`: `Σᵢ ext i ≤ ⌊2(n + δ)⌋`, stated here in the
  equivalent real form `(Σᵢ ext i : ℝ) ≤ 2 (n + δ)`.

The bound is then pure multiplicity counting:

* `δ < 1/2`: two top vertices would already need `ext`-mass `2n`,
  leaving nothing for the third vertex's mandatory cell; so at most
  one `k i = n - 1` and
  `Σ 2^{kᵢ} ≤ 2^{n-1} + 2·2^{n-2} = 2^n`.
* `δ < 1`: three top vertices would need `3n > 2n + 1` mass; so at
  most two and `Σ 2^{kᵢ} ≤ 2·2^{n-1} + 2^{n-2} = 5·2^{n-2}`.

These are exactly the `s = 3` instances of Sendov's two staircase
branches (`2^n` and `2^n + 2^{n-2}`), proved without any extremal-
profile assumption.
-/

namespace Jsp404

/-- The `s = 3` cell-data interface.  `n = ⌊π/λ⌋` and `δ` is the
fractional part of `π/λ`. -/
structure Base3CellData (n : ℕ) (δ : ℝ) where
  /-- Exterior-gap cell count at each vertex. -/
  ext : Fin 3 → ℕ
  /-- Exponent `k i = Σ_g max (m_g - 1) 0`. -/
  k : Fin 3 → ℕ
  /-- L1: the exterior gap always contains ≥ 1 cell. -/
  ext_pos : ∀ i, 1 ≤ ext i
  /-- L2: a top exponent `n - 1` forces exterior saturation. -/
  top_requires_sat : ∀ i, k i = n - 1 → ext i = n
  /-- L3: global exterior budget `Σᵢ ext i ≤ ⌊2(n + δ)⌋`
  (equivalent real form). -/
  ext_budget : ((Finset.univ.sum ext : ℕ) : ℝ) ≤ 2 * (n + δ)
  /-- Every exponent is at most `n - 1`. -/
  k_le : ∀ i, k i ≤ n - 1

variable {n : ℕ} {δ : ℝ} (D : Base3CellData n δ)

/-- `2 ^ k i ≤ 2 ^ (n-2)` when `i` is not a top vertex. -/
private lemma pow_le_of_ne_top (hn : 2 ≤ n) (i : Fin 3)
    (hi : D.k i ≠ n - 1) : (2 : ℕ) ^ D.k i ≤ 2 ^ (n - 2) := by
  have := D.k_le i
  have : D.k i ≤ n - 2 := by omega
  exact Nat.pow_le_pow_right (by norm_num) this

/-- **Low-δ branch**: `δ < 1/2` gives the sharp bound `Σ 2^{kᵢ} ≤ 2^n`. -/
theorem base3_low (hn : 2 ≤ n) (hδ : δ < 1 / 2) :
    ∑ i, (2 : ℕ) ^ D.k i ≤ 2 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  -- The exterior budget is at most `2n`.
  have hE : D.ext 0 + D.ext 1 + D.ext 2 ≤ 2 * (m + 2) := by
    have h := D.ext_budget
    rw [Fin.sum_univ_three] at h
    have hlt : D.ext 0 + D.ext 1 + D.ext 2 < 2 * (m + 2) + 1 := by
      by_contra hc
      push Not at hc
      have hcr : ((2 * (m + 2) + 1 : ℕ) : ℝ) ≤
          (D.ext 0 + D.ext 1 + D.ext 2 : ℕ) := by exact_mod_cast hc
      push_cast at hcr h
      linarith
    omega
  have h2m1 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
  have h2m2 : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by
    rw [show m + 2 = (m + 1) + 1 from rfl, pow_succ, h2m1]; ring
  rw [Fin.sum_univ_three, h2m2]
  by_cases h0 : D.k 0 = m + 1 <;>
    by_cases h1 : D.k 1 = m + 1 <;>
      by_cases h2 : D.k 2 = m + 1
  · -- all three top: `ext`-mass `3n > 2n`
    exfalso
    have e0 := D.top_requires_sat 0 h0
    have e1 := D.top_requires_sat 1 h1
    have e2 := D.top_requires_sat 2 h2
    omega
  · -- exactly two tops: `2n + 1 > 2n`
    exfalso
    have e0 := D.top_requires_sat 0 h0
    have e1 := D.top_requires_sat 1 h1
    have e2 := D.ext_pos 2
    omega
  · exfalso
    have e0 := D.top_requires_sat 0 h0
    have e2 := D.top_requires_sat 2 h2
    have e1 := D.ext_pos 1
    omega
  · -- only vertex 0 top
    have b1 : (2 : ℕ) ^ D.k 1 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 1 h1
    have b2 : (2 : ℕ) ^ D.k 2 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 2 h2
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ (m + 1) + 2 ^ m + 2 ^ m :=
          add_le_add (add_le_add (by rw [h0]) b1) b2
      _ = 4 * 2 ^ m := by rw [h2m1]; ring
  · exfalso
    have e1 := D.top_requires_sat 1 h1
    have e2 := D.top_requires_sat 2 h2
    have e0 := D.ext_pos 0
    omega
  · -- only vertex 1 top
    have b0 : (2 : ℕ) ^ D.k 0 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 0 h0
    have b2 : (2 : ℕ) ^ D.k 2 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 2 h2
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ m + 2 ^ (m + 1) + 2 ^ m :=
          add_le_add (add_le_add b0 (by rw [h1])) b2
      _ = 4 * 2 ^ m := by rw [h2m1]; ring
  · -- only vertex 2 top
    have b0 : (2 : ℕ) ^ D.k 0 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 0 h0
    have b1 : (2 : ℕ) ^ D.k 1 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 1 h1
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ m + 2 ^ m + 2 ^ (m + 1) :=
          add_le_add (add_le_add b0 b1) (by rw [h2])
      _ = 4 * 2 ^ m := by rw [h2m1]; ring
  · -- no tops
    have b0 : (2 : ℕ) ^ D.k 0 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 0 h0
    have b1 : (2 : ℕ) ^ D.k 1 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 1 h1
    have b2 : (2 : ℕ) ^ D.k 2 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 2 h2
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ m + 2 ^ m + 2 ^ m := add_le_add (add_le_add b0 b1) b2
      _ ≤ 4 * 2 ^ m := by omega

/-- **High-δ branch**: for any `δ < 1` the exterior budget is at most
`2n + 1`, which rules out three top vertices and gives
`Σ 2^{kᵢ} ≤ 5·2^{n-2}`. -/
theorem base3_high (hn : 2 ≤ n) (hδ : δ < 1) :
    ∑ i, (2 : ℕ) ^ D.k i ≤ 5 * 2 ^ (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hE : D.ext 0 + D.ext 1 + D.ext 2 ≤ 2 * (m + 2) + 1 := by
    have h := D.ext_budget
    rw [Fin.sum_univ_three] at h
    have hlt : D.ext 0 + D.ext 1 + D.ext 2 < 2 * (m + 2) + 2 := by
      by_contra hc
      push Not at hc
      have hcr : ((2 * (m + 2) + 2 : ℕ) : ℝ) ≤
          (D.ext 0 + D.ext 1 + D.ext 2 : ℕ) := by exact_mod_cast hc
      push_cast at hcr h
      linarith
    omega
  have h2m1 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
  rw [Fin.sum_univ_three]
  by_cases h0 : D.k 0 = m + 1 <;>
    by_cases h1 : D.k 1 = m + 1 <;>
      by_cases h2 : D.k 2 = m + 1
  · -- all three top: `ext`-mass `3n > 2n + 1` since `n ≥ 2`
    exfalso
    have e0 := D.top_requires_sat 0 h0
    have e1 := D.top_requires_sat 1 h1
    have e2 := D.top_requires_sat 2 h2
    omega
  · -- vertices 0,1 top: `2·2^{n-1} + 2^{n-2} = 5·2^{n-2}`
    have b2 : (2 : ℕ) ^ D.k 2 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 2 h2
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ (m + 1) + 2 ^ (m + 1) + 2 ^ m :=
          add_le_add (add_le_add (by rw [h0]) (by rw [h1])) b2
      _ = 5 * 2 ^ m := by rw [h2m1]; ring
  · have b1 : (2 : ℕ) ^ D.k 1 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 1 h1
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ (m + 1) + 2 ^ m + 2 ^ (m + 1) :=
          add_le_add (add_le_add (by rw [h0]) b1) (by rw [h2])
      _ = 5 * 2 ^ m := by rw [h2m1]; ring
  · have b1 : (2 : ℕ) ^ D.k 1 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 1 h1
    have b2 : (2 : ℕ) ^ D.k 2 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 2 h2
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ (m + 1) + 2 ^ m + 2 ^ m :=
          add_le_add (add_le_add (by rw [h0]) b1) b2
      _ ≤ 5 * 2 ^ m := by rw [h2m1]; omega
  · have b0 : (2 : ℕ) ^ D.k 0 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 0 h0
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ m + 2 ^ (m + 1) + 2 ^ (m + 1) :=
          add_le_add (add_le_add b0 (by rw [h1])) (by rw [h2])
      _ = 5 * 2 ^ m := by rw [h2m1]; ring
  · have b0 : (2 : ℕ) ^ D.k 0 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 0 h0
    have b2 : (2 : ℕ) ^ D.k 2 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 2 h2
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ m + 2 ^ (m + 1) + 2 ^ m :=
          add_le_add (add_le_add b0 (by rw [h1])) b2
      _ ≤ 5 * 2 ^ m := by rw [h2m1]; omega
  · have b0 : (2 : ℕ) ^ D.k 0 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 0 h0
    have b1 : (2 : ℕ) ^ D.k 1 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 1 h1
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ m + 2 ^ m + 2 ^ (m + 1) :=
          add_le_add (add_le_add b0 b1) (by rw [h2])
      _ ≤ 5 * 2 ^ m := by rw [h2m1]; omega
  · have b0 : (2 : ℕ) ^ D.k 0 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 0 h0
    have b1 : (2 : ℕ) ^ D.k 1 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 1 h1
    have b2 : (2 : ℕ) ^ D.k 2 ≤ 2 ^ m := pow_le_of_ne_top D (by omega) 2 h2
    calc 2 ^ D.k 0 + 2 ^ D.k 1 + 2 ^ D.k 2
        ≤ 2 ^ m + 2 ^ m + 2 ^ m := add_le_add (add_le_add b0 b1) b2
      _ ≤ 5 * 2 ^ m := by omega

end Jsp404
