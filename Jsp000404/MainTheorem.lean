import Jsp000404.GC

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
sharpness (there is a configuration whose largest angle is `≤ α(N)`).
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

/-- **Sendov's theorem (Erdős Problem 504), lower bound.** Every
configuration of `N` distinct points determines an angle at least
`alphaN N`. -/
theorem sendov_lower (N : ℕ) (hN : 3 ≤ N) :
    ∀ C : PtCfg, C.pts.length = N →
      ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
        p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  sorry

/-- **Sendov's theorem, sharpness.** There is a configuration of `N`
points all of whose angles are at most `alphaN N`. -/
theorem sendov_upper (N : ℕ) (hN : 3 ≤ N) :
    ∃ C : PtCfg, C.pts.length = N ∧
      ∀ p q r : Plane₂, p ∈ C.pts → q ∈ C.pts → r ∈ C.pts →
        p ≠ q → r ≠ q → p ≠ r → ∠ p q r ≤ alphaN N := by
  sorry

end Jsp404
