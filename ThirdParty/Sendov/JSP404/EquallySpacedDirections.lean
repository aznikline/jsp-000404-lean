import JSP404.DirectionalCover
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # Equally spaced unoriented direction lines -/

noncomputable section

namespace JSP404

open Real
open scoped RealInnerProductSpace

def circleDirection (θ : ℝ) : Point := !₂[cos θ, sin θ]

theorem norm_circleDirection (θ : ℝ) : ‖circleDirection θ‖ = 1 := by
  have h : ‖circleDirection θ‖ ^ 2 = 1 := by
    simp [EuclideanSpace.real_norm_sq_eq, circleDirection, Fin.sum_univ_two,
      Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (circleDirection θ)]

theorem angle_circleDirection (a b : ℝ) :
    InnerProductGeometry.angle (circleDirection a) (circleDirection b) =
      arccos (cos (a - b)) := by
  unfold InnerProductGeometry.angle
  rw [norm_circleDirection, norm_circleDirection]
  simp [circleDirection, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub, mul_comm]

theorem angle_circleDirection_le {a b δ : ℝ}
    (h : |a - b| ≤ δ) (hδ : δ ≤ π) :
    InnerProductGeometry.angle (circleDirection a) (circleDirection b) ≤ δ := by
  rw [angle_circleDirection, ← Real.cos_abs (a - b),
    Real.arccos_cos (abs_nonneg _) (h.trans hδ)]
  exact h

@[simp] theorem circleDirection_pi : circleDirection π = -circleDirection 0 := by
  ext i
  fin_cases i <;> simp [circleDirection]

/-- Polar coordinates in the closed upper half-plane. -/
theorem exists_polar_of_second_nonneg {x : Point} (hx : x ≠ 0) (hy : 0 ≤ x 1) :
    ∃ r θ : ℝ, 0 < r ∧ 0 ≤ θ ∧ θ ≤ π ∧ x = r • circleDirection θ := by
  let z : ℂ := ⟨x 0, x 1⟩
  have hz : z ≠ 0 := by
    intro h
    apply hx
    ext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  refine ⟨‖z‖, z.arg, norm_pos_iff.mpr hz, ?_, Complex.arg_le_pi _, ?_⟩
  · exact Complex.arg_nonneg_iff.mpr hy
  · ext i
    fin_cases i
    · simp [circleDirection, z]
    · simp [circleDirection, z]

/-- Round a point of [0,pi] to one of the k+1 grid endpoints. -/
theorem exists_near_grid {k : ℕ} (hk : 0 < k) {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ π) :
    ∃ j : ℕ, j ≤ k ∧ |θ - (j : ℝ) * π / k| ≤ π / (2 * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  let y : ℝ := θ * k / π
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hyk : y ≤ k := by
    dsimp [y]
    apply (div_le_iff₀ pi_pos).2
    nlinarith
  let j := ⌊y + 1 / 2⌋₊
  have hjlo : (j : ℝ) ≤ y + 1 / 2 := Nat.floor_le (by positivity)
  have hjhi : y + 1 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjk : j ≤ k := by
    have : (j : ℝ) < (k : ℝ) + 1 := by linarith
    have : j < k + 1 := by exact_mod_cast this
    omega
  refine ⟨j, hjk, ?_⟩
  have hdist : |y - (j : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    |θ - (j : ℝ) * π / k| = |(y - j) * π / k| := by
      congr 1
      dsimp [y]
      field_simp
    _ = |y - j| * π / k := by
      rw [abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos hk']
    _ ≤ (1 / 2 : ℝ) * π / k :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hdist pi_pos.le) hk'.le
    _ = π / (2 * k) := by ring

/-- The k equally spaced unoriented lines cover every vector direction within pi/(2k). -/
theorem equally_spaced_direction_cover (k : ℕ) (hk : 0 < k)
    (x : Point) (hx : x ≠ 0) :
    ∃ i : Fin k,
      InnerProductGeometry.angle x (circleDirection ((i : ℝ) * π / k)) ≤ π / (2 * k) ∨
      InnerProductGeometry.angle (-x) (circleDirection ((i : ℝ) * π / k)) ≤ π / (2 * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hδ : π / (2 * k) ≤ π := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).2
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [pi_pos]
  have upper : ∀ y : Point, y ≠ 0 → 0 ≤ y 1 → ∃ i : Fin k,
      InnerProductGeometry.angle y (circleDirection ((i : ℝ) * π / k)) ≤ π / (2 * k) ∨
      InnerProductGeometry.angle (-y) (circleDirection ((i : ℝ) * π / k)) ≤ π / (2 * k) := by
    intro y hy hy₁
    obtain ⟨r, θ, hr, hθ, hθπ, hyr⟩ := exists_polar_of_second_nonneg hy hy₁
    obtain ⟨j, hj, hclose⟩ := exists_near_grid hk hθ hθπ
    have ha : InnerProductGeometry.angle y (circleDirection ((j : ℝ) * π / k)) ≤
        π / (2 * k) := by
      rw [hyr, InnerProductGeometry.angle_smul_left_of_pos _ _ hr]
      exact angle_circleDirection_le hclose hδ
    by_cases hjk : j < k
    · exact ⟨⟨j, hjk⟩, Or.inl ha⟩
    · have heq : j = k := by omega
      subst j
      have hpi : (k : ℝ) * π / k = π := by field_simp
      rw [hpi, circleDirection_pi, InnerProductGeometry.angle_neg_right] at ha
      refine ⟨⟨0, hk⟩, Or.inr ?_⟩
      simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_div,
        InnerProductGeometry.angle_neg_left] using ha
  by_cases hy : 0 ≤ x 1
  · exact upper x hx hy
  · obtain ⟨i, hi | hi⟩ := upper (-x) (by simpa) (by simpa using (le_of_not_ge hy))
    · exact ⟨i, Or.inr hi⟩
    · exact ⟨i, Or.inl (by simpa using hi)⟩

/-- The classical exponential-cardinality lower bound on the extremal angle. -/
theorem szekeres_lower_bound (n k : ℕ) (hk : 2 ≤ k) (hn : 2 ^ k < n) :
    Guaranteed n ((1 - 1 / (k : ℝ)) * π) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hδ : π / (2 * k) < π / 2 := by
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * k) (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [pi_pos]
  have h := guaranteed_of_direction_cover n k
    (fun i => circleDirection ((i : ℝ) * π / k)) (π / (2 * k)) hδ hn
    (equally_spaced_direction_cover k (by omega))
  convert h using 1
  ring

/-- Exact angle between two grid directions, which lie in a common half-circle. -/
theorem angle_grid_directions {k : ℕ} (hk : 0 < k) (i j : Fin k) :
    InnerProductGeometry.angle (circleDirection ((i : ℝ) * π / k))
      (circleDirection ((j : ℝ) * π / k)) = |(i : ℝ) - j| * π / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hi : (i : ℝ) ≤ (k : ℝ) - 1 := by
    have h : (i : ℕ) + 1 ≤ k := i.isLt
    have h' : (i : ℝ) + 1 ≤ k := by exact_mod_cast h
    linarith
  have hj : (j : ℝ) ≤ (k : ℝ) - 1 := by
    have h : (j : ℕ) + 1 ≤ k := j.isLt
    have h' : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
    linarith
  have hd : |(i : ℝ) - j| ≤ (k : ℝ) - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hδ : |(i : ℝ) - j| * π / k ≤ π := by
    apply (div_le_iff₀ hk').2
    nlinarith [mul_le_mul_of_nonneg_right hd pi_pos.le, pi_pos]
  have heq : |(i : ℝ) * π / k - (j : ℝ) * π / k| = |(i : ℝ) - j| * π / k := by
    rw [← sub_div, ← sub_mul, abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos hk']
  rw [angle_circleDirection, ← cos_abs, arccos_cos (abs_nonneg _) (by simpa [heq] using hδ)]
  exact heq

theorem grid_direction_angle_bounds {k : ℕ} (hk : 2 ≤ k) {i j : Fin k} (hij : i ≠ j) :
    π / k ≤ InnerProductGeometry.angle (circleDirection ((i : ℝ) * π / k))
      (circleDirection ((j : ℝ) * π / k)) ∧
    InnerProductGeometry.angle (circleDirection ((i : ℝ) * π / k))
      (circleDirection ((j : ℝ) * π / k)) ≤ (1 - 1 / (k : ℝ)) * π := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [angle_grid_directions (by omega)]
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hi : (i : ℝ) + 1 ≤ k := by exact_mod_cast i.isLt
  have hj : (j : ℝ) + 1 ≤ k := by exact_mod_cast j.isLt
  have hupper : |(i : ℝ) - j| ≤ (k : ℝ) - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hlower : (1 : ℝ) ≤ |(i : ℝ) - j| := by
    have hv : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hij | hji
    · have h : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      rw [abs_of_nonpos (by linarith : (i : ℝ) - j ≤ 0)]
      linarith
    · have h : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
      rw [abs_of_nonneg (by linarith : 0 ≤ (i : ℝ) - j)]
      linarith
  constructor
  · exact div_le_div_of_nonneg_right (by nlinarith [pi_pos]) hk'.le
  · calc
      |(i : ℝ) - j| * π / k ≤ ((k : ℝ) - 1) * π / k :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hupper pi_pos.le) hk'.le
      _ = (1 - 1 / (k : ℝ)) * π := by field_simp

/-- Arbitrary signs on two different direction lines still satisfy the desired upper bound. -/
theorem signed_grid_direction_angle_le {k : ℕ} (hk : 2 ≤ k) {i j : Fin k} (hij : i ≠ j)
    (a b : Bool) :
    InnerProductGeometry.angle
      (if a then circleDirection ((i : ℝ) * π / k) else -circleDirection ((i : ℝ) * π / k))
      (if b then circleDirection ((j : ℝ) * π / k) else -circleDirection ((j : ℝ) * π / k)) ≤
      (1 - 1 / (k : ℝ)) * π := by
  obtain ⟨hlo, hhi⟩ := grid_direction_angle_bounds hk hij
  have ht : (1 - 1 / (k : ℝ)) * π = π - π / k := by ring
  rw [ht] at hhi ⊢
  cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
    InnerProductGeometry.angle_neg_left,
    InnerProductGeometry.angle_neg_right] <;> linarith

theorem signed_grid_direction_angle_le_real {k : ℕ} (hk : 2 ≤ k) {i j : Fin k}
    (hij : i ≠ j) (r s : ℝ) (hr : r = -1 ∨ r = 1) (hs : s = -1 ∨ s = 1) :
    InnerProductGeometry.angle
      (r • circleDirection ((i : ℝ) * π / k))
      (s • circleDirection ((j : ℝ) * π / k)) ≤ (1 - 1 / (k : ℝ)) * π := by
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · simpa only [neg_one_smul, Bool.false_eq_true, ↓reduceIte] using
      signed_grid_direction_angle_le hk hij false false
  · simpa only [neg_one_smul, one_smul, Bool.false_eq_true, ↓reduceIte] using
      signed_grid_direction_angle_le hk hij false true
  · simpa only [neg_one_smul, one_smul, Bool.false_eq_true, ↓reduceIte] using
      signed_grid_direction_angle_le hk hij true false
  · simpa only [one_smul, ↓reduceIte] using
      signed_grid_direction_angle_le hk hij true true

end JSP404
