import JSP404.BinaryConstruction
import JSP404.EquallySpacedDirections

/-!
# Explicit classical bounds on the actual planar extremal angle

The upper bound instantiates the multiscale construction with equally spaced
unoriented lines. Combined with the direction-cover lower bound, it brackets
the extremal angle for every range between consecutive powers of two.
These estimates are not Sendov's complete sharp classification.
-/

noncomputable section

open Real

namespace JSP404

theorem three_le_two_pow {k : ℕ} (hk : 2 ≤ k) : 3 ≤ 2 ^ k := by
  have hp : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  norm_num at hp
  omega

/-- A concrete multiscale construction yields the classical power-of-two upper bound. -/
theorem szekeres_upper_bound (k : ℕ) (hk : 2 ≤ k) :
    alpha (2 ^ k) ≤ (1 - 1 / (k : ℝ)) * π := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoef : 0 ≤ 1 - 1 / (k : ℝ) := by
    have hh : 1 / (k : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  apply alpha_two_pow_le_of_signed_directions
    (fun i : Fin k => circleDirection ((i : ℝ) * π / k))
    (fun i => norm_ne_zero_iff.mp (by rw [norm_circleDirection]; norm_num))
    (three_le_two_pow hk) (mul_nonneg hcoef pi_pos.le)
  intro i j hij r s hr hs
  exact signed_grid_direction_angle_le_real hk hij r s hr hs

/-- Selecting subsets transfers the upper bound to every smaller admissible cardinality. -/
theorem alpha_le_szekeres_upper {N k : ℕ} (hN : 3 ≤ N) (hk : 2 ≤ k)
    (hNk : N ≤ 2 ^ k) : alpha N ≤ (1 - 1 / (k : ℝ)) * π :=
  (alpha_mono hN hNk).trans (szekeres_upper_bound k hk)

/-- The direction-cover theorem interpreted as a lower bound on the extremal quantity. -/
theorem szekeres_lower_bound_alpha {N k : ℕ} (hk : 2 ≤ k) (hNk : 2 ^ k < N) :
    (1 - 1 / (k : ℝ)) * π ≤ alpha N :=
  le_alpha (szekeres_lower_bound N k hk hNk)

/-- Explicit two-sided bounds for cardinalities between consecutive powers of two. -/
theorem classical_bounds_between_powers {N k : ℕ} (hk : 2 ≤ k)
    (hlo : 2 ^ k < N) (hhi : N ≤ 2 ^ (k + 1)) :
    (1 - 1 / (k : ℝ)) * π ≤ alpha N ∧
      alpha N ≤ (1 - 1 / ((k + 1 : ℕ) : ℝ)) * π := by
  refine ⟨szekeres_lower_bound_alpha hk hlo, ?_⟩
  have hN : 3 ≤ N := le_trans (three_le_two_pow hk) hlo.le
  exact alpha_le_szekeres_upper hN (by omega) hhi

/-- A simple bound applicable without choosing a separate logarithmic parameter. -/
theorem alpha_le_self_index_upper {N : ℕ} (hN : 3 ≤ N) :
    alpha N ≤ (1 - 1 / (N : ℝ)) * π := by
  exact alpha_le_szekeres_upper hN (by omega) (Nat.lt_two_pow_self.le)

/-- Every finite admissible cardinality has extremal angle strictly below a straight angle. -/
theorem alpha_lt_pi {N : ℕ} (hN : 3 ≤ N) : alpha N < π := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpos : 0 < 1 / (N : ℝ) * π := mul_pos (by positivity) pi_pos
  exact (alpha_le_self_index_upper hN).trans_lt (by nlinarith)

end JSP404
