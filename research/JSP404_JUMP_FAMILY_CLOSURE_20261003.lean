import Jsp000404.SmallAngleLower

/-!
# Conditional closure from the two ordinary-point jump families

This file proves only the consumer of two explicit geometric hypotheses.
It does not prove either jump family. The initial range `3 ≤ N ≤ 8` uses
the existing unconditional lower bound; larger cardinalities use monotonicity
of `JSP404.Guaranteed` within their `Nat.clog` bands.

The arithmetic route and integer-to-natural exponent bridge were checked
independently by the same-task collaborator `jsp404_low_route_audit` in
`/tmp/jsp404_oct3_endpoint_values.lean`; the consumer below records its own
proofs in the project environment.
-/

open scoped EuclideanGeometry

namespace Jsp404

/-- Conditional universal lower bound for every original cardinality.
Both hypotheses concern actual distinct planar points and remain explicit:
the low jump is at `2^n + 1`, and the high jump at `2^n + 2^(n-2) + 1`.
The strip `n = 2` is already covered by the unconditional initial range. -/
theorem guaranteed_alphaN_of_jump_families
    (hLow : ∀ n : ℕ, 3 ≤ n →
      JSP404.Guaranteed (2 ^ n + 1)
        ((1 - 2 / (2 * n + 1 : ℝ)) * Real.pi))
    (hHigh : ∀ n : ℕ, 3 ≤ n →
      JSP404.Guaranteed (2 ^ n + 2 ^ (n - 2) + 1)
        ((1 - 1 / (n + 1 : ℝ)) * Real.pi))
    (N : ℕ) (hN : 3 ≤ N) :
    JSP404.Guaranteed N (alphaN N) := by
  by_cases hN8 : N ≤ 8
  · rw [← sendov_alpha_eq_le_eight N hN hN8]
    exact JSP404.guaranteed_alpha hN
  have hN9 : 9 ≤ N := by omega
  let n := Nat.clog 2 N - 1
  have hclog : 4 ≤ Nat.clog 2 N := by
    have hmono := Nat.clog_mono_right 2 hN9
    have h9 : Nat.clog 2 9 = 4 := by decide
    omega
  have hn3 : 3 ≤ n := by dsimp [n]; omega
  have hNlo : 2 ^ n < N :=
    Nat.pow_lt_of_lt_clog (by dsimp [n]; omega)
  rw [alphaN_of_ge_four (by omega) (n := n) rfl]
  by_cases hbr : (N : ℝ) ≤ (2 : ℝ) ^ n + (2 : ℝ) ^ ((n : ℤ) - 2)
  · rw [if_pos hbr]
    exact JSP404.guaranteed_mono (by omega : 2 ^ n + 1 ≤ N) (hLow n hn3)
  · rw [if_neg hbr]
    have hcast : (n : ℤ) - 2 = ((n - 2 : ℕ) : ℤ) := by omega
    have hreal : (2 : ℝ) ^ n + (2 : ℝ) ^ ((n : ℤ) - 2) < (N : ℝ) :=
      lt_of_not_ge hbr
    rw [hcast, zpow_natCast] at hreal
    have hNgt : (2 : ℕ) ^ n + 2 ^ (n - 2) < N := by
      exact_mod_cast hreal
    exact JSP404.guaranteed_mono
      (by omega : 2 ^ n + 2 ^ (n - 2) + 1 ≤ N) (hHigh n hn3)

/-- Conditional equality for the genuine supremum of universally guaranteed
Euclidean angles. Sharpness is supplied by the existing unconditional upper
bound; the lower bound is conditional on both jump families. -/
theorem sendov_alpha_eq_of_jump_families
    (hLow : ∀ n : ℕ, 3 ≤ n →
      JSP404.Guaranteed (2 ^ n + 1)
        ((1 - 2 / (2 * n + 1 : ℝ)) * Real.pi))
    (hHigh : ∀ n : ℕ, 3 ≤ n →
      JSP404.Guaranteed (2 ^ n + 2 ^ (n - 2) + 1)
        ((1 - 1 / (n + 1 : ℝ)) * Real.pi))
    (N : ℕ) (hN : 3 ≤ N) :
    JSP404.alpha N = alphaN N :=
  le_antisymm (alpha_le_alphaN N hN)
    (JSP404.le_alpha (guaranteed_alphaN_of_jump_families hLow hHigh N hN))

/-- The conditional lower consumer in the original point-list interface,
including every membership and pairwise-distinctness condition. -/
theorem sendov_lower_of_jump_families
    (hLow : ∀ n : ℕ, 3 ≤ n →
      JSP404.Guaranteed (2 ^ n + 1)
        ((1 - 2 / (2 * n + 1 : ℝ)) * Real.pi))
    (hHigh : ∀ n : ℕ, 3 ≤ n →
      JSP404.Guaranteed (2 ^ n + 2 ^ (n - 2) + 1)
        ((1 - 1 / (n + 1 : ℝ)) * Real.pi))
    (N : ℕ) (hN : 3 ≤ N) (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  classical
  have hs : C.pts.toFinset.card = N := by
    rw [List.toFinset_card_of_nodup C.nodup]
    exact hlen
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, hang⟩ :=
    guaranteed_alphaN_of_jump_families hLow hHigh N hN C.pts.toFinset hs
  exact ⟨p, q, r, List.mem_toFinset.mp hp, List.mem_toFinset.mp hq,
    List.mem_toFinset.mp hr, hpq, hqr.symm, hpr, hang⟩

/-- The complete original lower-and-sharpness statement, conditional only
on the two explicitly supplied ordinary-point jump families. -/
theorem sendov_of_jump_families
    (hLow : ∀ n : ℕ, 3 ≤ n →
      JSP404.Guaranteed (2 ^ n + 1)
        ((1 - 2 / (2 * n + 1 : ℝ)) * Real.pi))
    (hHigh : ∀ n : ℕ, 3 ≤ n →
      JSP404.Guaranteed (2 ^ n + 2 ^ (n - 2) + 1)
        ((1 - 1 / (n + 1 : ℝ)) * Real.pi))
    (N : ℕ) (hN : 3 ≤ N) :
    (∀ C : PtCfg, C.pts.length = N →
      ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
        p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : PtCfg, C.pts.length = N ∧
      ∀ p q r : Plane₂, p ∈ C.pts → q ∈ C.pts → r ∈ C.pts →
        p ≠ q → r ≠ q → p ≠ r → ∠ p q r < alphaN N + ε) :=
  ⟨fun C hlen => sendov_lower_of_jump_families hLow hHigh N hN C hlen,
    sendov_upper N hN⟩

#print axioms guaranteed_alphaN_of_jump_families
#print axioms sendov_alpha_eq_of_jump_families
#print axioms sendov_lower_of_jump_families
#print axioms sendov_of_jump_families

end Jsp404
