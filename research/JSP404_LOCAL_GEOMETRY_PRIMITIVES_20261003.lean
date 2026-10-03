import Jsp000404.Statement
import Jsp000404.AcuteFanPacking
import Jsp000404.WeightedCircleSeparation
import Jsp000404.TriangleRestriction
import Jsp000404.IntervalPacking

/-!
# October 3 local geometry and ordinary jump arithmetic

These are bounded, independently checkable primitives. No theorem below
proves a new ordinary endpoint, a positive-row count, or a global capacity.
The endpoint values identify the two ordinary-point obligations that a
full Sendov proof must discharge. The remaining lemmas supply local
pieces for a third-strip positive-row/diameter argument.

Still to construct from actual geometry:

* A positive cyclic row score supplies a projective gap `G >= 2 * lam`.
  Rotate its complementary line interval into `[0,H]`, `H = pi-G`,
  and derive actual lift labels and their opposite-label distance bound.
  `lift_classes_separated` then orders those two classes when `H < 2*lam`.
* Turn that ordered lift data into an actual directed ray window of width
  at most `pi-lam`. The window must be for the actual vectors, not just
  their unoriented line representatives.
* At an actual diameter endpoint, use `diameter_ray_acute` and the occupied
  diameter ray to show every internal fan gap is below `pi/2`. In strip
  three, any score-producing gap is consequently the exterior fan gap;
  derive the sharper window width `pi-(k+1)*lam` there.
* Supply those constructed windows to `turn_budget_of_ray_windows`, then
  restrict to positive rows to obtain the proposed positive-row counts.
  None of these geometry-to-window or restriction/count steps is asserted
  as already proved by this file.

The positive-row angle exclusions are unconditional consequences of the
actual row score. Their signatures contain no capacity or certificate input.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.Oct3Local

lemma clog_band {N n : ℕ} (hlo : 2 ^ n < N) (hhi : N ≤ 2 ^ (n+1)) :
    Nat.clog 2 N - 1 = n := by
  have hl : n < Nat.clog 2 N :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlo
  have hh : Nat.clog 2 N ≤ n + 1 :=
    (Nat.clog_le_iff_le_pow (by norm_num)).mpr hhi
  omega

private lemma pow_four (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℕ)^n = 4 * 2 ^ (n-2) := by
  have he : n = (n-2)+2 := by omega
  conv_lhs => rw [he]
  rw [pow_add]
  ring

/-- The first cardinality in every later lower plateau. This evaluates
the formula; it does not prove that this angle is guaranteed. -/
lemma alphaN_low_jump (n : ℕ) (hn : 3 ≤ n) :
    alphaN (2 ^ n + 1) = (1 - 2 / (2 * n + 1 : ℝ)) * Real.pi := by
  have hp : 1 ≤ (2 : ℕ) ^ (n-2) := Nat.one_le_two_pow
  have hpow := pow_four n (by omega)
  have hp' : 4 ≤ (2 : ℕ) ^ n := by omega
  have hclog : Nat.clog 2 (2^n+1) - 1 = n :=
    clog_band (by omega) (by rw [pow_succ]; omega)
  rw [alphaN_of_ge_four (by omega) hclog.symm]
  have hcast : (n : ℤ) - 2 = ((n-2 : ℕ) : ℤ) := by omega
  have hbr : ((2 ^ n + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ n + (2 : ℝ) ^ ((n : ℤ)-2) := by
    rw [hcast, zpow_natCast]
    exact_mod_cast (show (2 : ℕ)^n+1 ≤ 2^n+2^(n-2) by omega)
  rw [ite_eq_left hbr]

/-- The first cardinality in every later upper plateau. Again this is
formula arithmetic, with no new guaranteed-angle assertion. -/
lemma alphaN_high_jump (n : ℕ) (hn : 3 ≤ n) :
    alphaN (2 ^ n + 2 ^ (n-2) + 1) =
      (1 - 1 / (n + 1 : ℝ)) * Real.pi := by
  have hp : 1 ≤ (2 : ℕ) ^ (n-2) := Nat.one_le_two_pow
  have hpow := pow_four n (by omega)
  have hp' : 4 ≤ (2 : ℕ) ^ n := by omega
  have hclog : Nat.clog 2 (2^n+2^(n-2)+1) - 1 = n :=
    clog_band (by omega) (by rw [pow_succ]; omega)
  rw [alphaN_of_ge_four (by omega) hclog.symm]
  have hcast : (n : ℤ) - 2 = ((n-2 : ℕ) : ℤ) := by omega
  have hbr : ¬ ((2 ^ n + 2^(n-2) + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ n + (2 : ℝ) ^ ((n : ℤ)-2) := by
    rw [hcast, zpow_natCast]
    exact_mod_cast (show ¬(2 : ℕ)^n+2^(n-2)+1 ≤ 2^n+2^(n-2) by omega)
  rw [ite_eq_right hbr]

/-- A diameter comparison gives a quantitative positive projection. -/
lemma diameter_projection_lower {A B P : Plane₂}
    (hdiam : ‖P - B‖ ≤ ‖A - B‖) :
    ‖P - A‖ ^ 2 / 2 ≤ inner (𝕜 := ℝ) (P - A) (B - A) := by
  have he : (P - A) - (B - A) = P - B := by abel
  have hs := norm_sub_sq_real (P - A) (B - A)
  rw [he] at hs
  rw [norm_sub_rev A B] at hdiam
  have hsq : ‖P - B‖ ^ 2 ≤ ‖B - A‖ ^ 2 := by gcongr
  nlinarith

/-- Every nonzero outgoing ray at a diameter endpoint makes a strictly
acute angle with the diameter ray. -/
lemma diameter_ray_acute {A B P : Plane₂}
    (hdiam : ‖P - B‖ ≤ ‖A - B‖) (hPA : P ≠ A) :
    InnerProductGeometry.angle (P - A) (B - A) < Real.pi / 2 := by
  have hb := diameter_projection_lower hdiam
  have hnorm : 0 < ‖P - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hPA)
  have hip : 0 < inner (𝕜 := ℝ) (P - A) (B - A) := by nlinarith
  by_contra hn
  have hangle : Real.pi / 2 ≤
      InnerProductGeometry.angle (P - A) (B - A) := le_of_not_gt hn
  have hnip := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr hangle
  linarith

/-- Opposite lifts cannot interleave in a projective window shorter
than twice the required opposite-lift separation. -/
lemma lift_classes_separated {ι : Type*} (x : ι → ℝ) (bit : ι → Bool)
    {lam H : ℝ} (hH : H < 2 * lam)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ H) (z : ι) (hz : x z = 0)
    (hop : ∀ i j, bit i ≠ bit j → lam ≤ |x i - x j|) :
    ∀ i j, bit i = bit z → bit j ≠ bit z → x i + lam ≤ x j := by
  intro i j hi hj
  have hjlam : lam ≤ x j := by
    have hh := hop z j hj.symm
    rw [hz, zero_sub, abs_neg, abs_of_nonneg (hx j).1] at hh
    exact hh
  have hdist := hop i j (by simpa only [hi] using hj.symm)
  by_cases hij : x i ≤ x j
  · rw [abs_of_nonpos (sub_nonpos.mpr hij)] at hdist
    linarith
  · have hij' : x j < x i := lt_of_not_ge hij
    rw [abs_of_nonneg (sub_nonneg.mpr hij'.le)] at hdist
    linarith [(hx i).2]

/-- Actual local inward bisectors have a circle budget without the
120-degree bound used to construct unrestricted fans elsewhere. -/
lemma actual_bisector_turn_budget {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 2 ≤ s)
    (c m : Fin s → Plane₂) (hm : ∀ i, m i ≠ 0) (a : Fin s → ℝ)
    (hbound : ∀ i j, j ≠ i →
      InnerProductGeometry.angle (m i) (c j-c i) ≤ a i/2) :
    ∑ i, (Real.pi - a i) ≤ 2 * Real.pi := by
  apply weighted_circle_separation_bound o hs m hm (fun i => Real.pi - a i)
  intro i j hij
  have hi := hbound i j hij.symm
  have hj := hbound j i hij
  have hneg : InnerProductGeometry.angle (m j) (c j-c i) =
      Real.pi-InnerProductGeometry.angle (m j) (c i-c j) := by
    rw [show c j-c i = -(c i-c j) by abel, InnerProductGeometry.angle_neg_right]
  have ht := InnerProductGeometry.angle_le_angle_add_angle (m j) (m i) (c j-c i)
  rw [hneg, InnerProductGeometry.angle_comm (m j) (m i)] at ht
  linarith

/-- Explicit actual ray windows supply the local bisectors and their
turn budget. The windows are inputs, not assumed to follow from a row score. -/
lemma turn_budget_of_ray_windows {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 2 ≤ s)
    (c : Fin s → Plane₂) (hinj : Function.Injective c)
    (a : Fin s → ℝ) (ha : ∀ i, 0 ≤ a i) (hapi : ∀ i, a i < Real.pi)
    (e : Fin s → Plane₂) (he : ∀ i, e i ≠ 0)
    (theta : (i : Fin s) → {j : Fin s // j ≠ i} → ℝ)
    (htheta : ∀ i j, theta i j ∈ Set.Icc 0 (a i) ∧
      o.oangle (e i) (c j-c i) = (theta i j : Real.Angle)) :
    ∑ i, (Real.pi - a i) ≤ 2 * Real.pi := by
  classical
  have hlocal (i : Fin s) : ∃ m : Plane₂, m ≠ 0 ∧
      ∀ j : Fin s, j ≠ i →
        InnerProductGeometry.angle m (c j-c i) ≤ a i/2 := by
    let u : {j : Fin s // j ≠ i} → Plane₂ := fun j => c j-c i
    have hu (j : {j : Fin s // j ≠ i}) : u j ≠ 0 :=
      sub_ne_zero.mpr (hinj.ne j.property)
    obtain ⟨m, hm, hb⟩ := exists_inward_bisector_of_ray_window o u hu
      (ha i) (hapi i) (e i) (he i) (theta i) (htheta i)
    exact ⟨m, hm, fun j hj => hb ⟨j, hj⟩⟩
  choose m hm hb using hlocal
  exact actual_bisector_turn_budget o hs c m hm a hb

/-- Any angle at a positive actual row lies outside the open band in
which both complementary arcs have zero gap score. -/
lemma positive_row_angle_outside {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    {lam : ℝ} (hlam : 0 < lam) {i j k : Fin s}
    (hij : i ≠ j) (hik : i ≠ k)
    (hpos : 0 < rowScore lam (directionRow o e c i)) :
    ∠ (c j) (c i) (c k) ≤ Real.pi - 2 * lam ∨
      2 * lam ≤ ∠ (c j) (c i) (c k) := by
  by_contra h
  push Not at h
  have hA : gapScore lam (∠ (c j) (c i) (c k)) ≤ 0 :=
    gapScore_le_of_lt_mul hlam 0 (by simpa using h.2)
  have hB : gapScore lam (Real.pi - ∠ (c j) (c i) (c k)) ≤ 0 :=
    gapScore_le_of_lt_mul hlam 0 (by norm_num; linarith [h.1])
  have hr := rowScore_le_triangle_arcs o e hlam hinj he hij hik
  omega

/-- In the third LOW strip the whole closed 3pi/7 through 4pi/7 band
is excluded at every positive row. The conclusion is strict at both ends. -/
lemma positive_row_excludes_low_fixed_band {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    {lam : ℝ} (hlam : 0 < lam) (hlow : 2 * Real.pi / 7 < lam)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k)
    (hpos : 0 < rowScore lam (directionRow o e c i)) :
    ∠ (c j) (c i) (c k) < 3 * Real.pi / 7 ∨
      4 * Real.pi / 7 < ∠ (c j) (c i) (c k) := by
  rcases positive_row_angle_outside o e he hinj hlam hij hik hpos with h | h
  · left; linarith
  · right; linarith

#print axioms clog_band
#print axioms alphaN_low_jump
#print axioms alphaN_high_jump
#print axioms diameter_projection_lower
#print axioms diameter_ray_acute
#print axioms lift_classes_separated
#print axioms actual_bisector_turn_budget
#print axioms turn_budget_of_ray_windows
#print axioms positive_row_angle_outside
#print axioms positive_row_excludes_low_fixed_band

end Jsp404.Oct3Local
