import Jsp000404.GC
import Mathlib.Tactic

/-!
# Sendov's theorem — the target statement (Erdős problem 504)

Blumenthal's problem asks for `α(N)`: the largest angle that every planar
configuration of `N` points must determine. Sendov (1995) proved

- `α(N) = (1 - 2/(2n+1))·π`  for `2^n < N ≤ 2^n + 2^{n-2}`,
- `α(N) = (1 - 1/(n+1))·π`   for `2^n + 2^{n-2} < N ≤ 2^{n+1}`,

for `N ≥ 4`, where `n` is determined by `2^n < N ≤ 2^{n+1}`; and
`α(3) = π/3`.

NOTE on the catalogue: erdosproblems.com/504 prints the first branch with
numerator `1` (`π(1 - 1/(2n-1))`), which is wrong — e.g. at `N = 5` it gives
`4π/5` while the true value is `3π/5`. The formula below is Sendov's
Theorem 4.1 as printed in Acta Math. Hungar. 69 (1995).

The theorem is stated as the conjunction of a lower bound (every
configuration of `N` distinct points determines an angle `≥ α(N)`) and
sharpness (for every positive error there is a configuration whose largest
angle is less than `α(N)` plus that error). This is the sharp universal
threshold; exact attainment by an ordinary configuration is not required.
-/

open scoped EuclideanGeometry

namespace Jsp404

/-- The piecewise formula for Sendov's minimax angle, valid for `N ≥ 3`.
For `N = 3` the value is `π/3`; for `N ≥ 4` the piecewise formula of
Sendov's Theorem 4.1 applies, with `n` the unique natural number
satisfying `2^n < N ≤ 2^{n+1}`. -/
noncomputable def alphaN : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => Real.pi / 3
  | N + 4 =>
    let n := Nat.clog 2 (N + 4) - 1
    if (N + 4 : ℝ) ≤ 2 ^ n + 2 ^ ((n : ℤ) - 2) then
      (1 - 2 / (2 * n + 1 : ℝ)) * Real.pi
    else
      (1 - 1 / (n + 1 : ℝ)) * Real.pi

/-- A finite plane configuration: a list of distinct points. -/
structure PtCfg where
  pts : List Plane₂
  nodup : pts.Nodup
  len : 3 ≤ pts.length

/-- Unfold `alphaN` on the `N + 4` branch, with the `let` zeta-reduced. -/
lemma alphaN_succ_add (m : ℕ) :
    alphaN (m + 4) =
      if ((m : ℝ) + 4) ≤ 2 ^ (Nat.clog 2 (m + 4) - 1) +
          (2 : ℝ) ^ (((Nat.clog 2 (m + 4) - 1 : ℕ) : ℤ) - 2) then
        (1 - 2 / (2 * ((Nat.clog 2 (m + 4) - 1 : ℕ) : ℝ) + 1)) * Real.pi
      else
        (1 - 1 / (((Nat.clog 2 (m + 4) - 1 : ℕ) : ℝ) + 1)) * Real.pi :=
  rfl

/-- Unfold `alphaN` in the `N ≥ 4` branch, named by `n = Nat.clog 2 N - 1`. -/
lemma alphaN_of_ge_four {N n : ℕ} (hN : 4 ≤ N) (hn : n = Nat.clog 2 N - 1) :
    alphaN N = if (N : ℝ) ≤ 2 ^ n + 2 ^ ((n : ℤ) - 2) then
        (1 - 2 / (2 * n + 1 : ℝ)) * Real.pi
      else (1 - 1 / ((n : ℝ) + 1)) * Real.pi := by
  subst hn
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 4 := ⟨N - 4, by omega⟩
  rw [alphaN_succ_add]
  simp only [Nat.cast_add, Nat.cast_ofNat]

/-- `alphaN N < π` for `N ≥ 4`. -/
lemma alphaN_lt_pi {N : ℕ} (hN : 4 ≤ N) : alphaN N < Real.pi := by
  rw [alphaN_of_ge_four hN (n := Nat.clog 2 N - 1) rfl]
  by_cases h : (N : ℝ) ≤ 2 ^ (Nat.clog 2 N - 1) +
      (2 : ℝ) ^ (((Nat.clog 2 N - 1 : ℕ) : ℤ) - 2)
  · rw [if_pos h]
    have hx : (0 : ℝ) < 2 / (2 * ((Nat.clog 2 N - 1 : ℕ) : ℝ) + 1) := by
      positivity
    calc (1 - 2 / (2 * ((Nat.clog 2 N - 1 : ℕ) : ℝ) + 1)) * Real.pi
        < 1 * Real.pi := by
          apply mul_lt_mul_of_pos_right _ Real.pi_pos
          linarith
      _ = Real.pi := one_mul _
  · rw [if_neg h]
    have hx : (0 : ℝ) < 1 / (((Nat.clog 2 N - 1 : ℕ) : ℝ) + 1) := by
      positivity
    calc (1 - 1 / (((Nat.clog 2 N - 1 : ℕ) : ℝ) + 1)) * Real.pi
        < 1 * Real.pi := by
          apply mul_lt_mul_of_pos_right _ Real.pi_pos
          linarith
      _ = Real.pi := one_mul _

end Jsp404
