import JSP404.ClusterConstruction
import JSP404.EquallySpacedDirections
import JSP404.ClassicalBounds

/-!
# The three-center construction for the intermediate interval

This module formalizes Sendov's three-center construction from
*Compulsory configurations of points in the plane* (1995), Lemma 4.14,
and combines it with the classical binary construction. It proves the upper
bounds in both intervals of the classification formula. The matching sharp
universal lower bounds are not proved here.
-/

noncomputable section

open Real

namespace JSP404

theorem signed_circleDirection_angle_le_of_separation {a b δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : δ ≤ |a - b|) (hhi : |a - b| ≤ π - δ)
    (r s : ℝ) (hr : r = -1 ∨ r = 1) (hs : s = -1 ∨ s = 1) :
    InnerProductGeometry.angle (r • circleDirection a) (s • circleDirection b) ≤ π - δ := by
  have hang : InnerProductGeometry.angle (circleDirection a) (circleDirection b) = |a - b| := by
    rw [angle_circleDirection, ← Real.cos_abs (a - b),
      Real.arccos_cos (abs_nonneg _) (by linarith)]
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;>
    simp only [neg_one_smul, one_smul, InnerProductGeometry.angle_neg_left,
      InnerProductGeometry.angle_neg_right, hang] <;> linarith

def threeClusterPhi (n : ℕ) : ℝ := π / (2 * (n : ℝ) + 1)

theorem threeClusterPhi_pos (n : ℕ) : 0 < threeClusterPhi n := by
  unfold threeClusterPhi
  positivity

theorem threeClusterPhi_mul (n : ℕ) : (2 * (n : ℝ) + 1) * threeClusterPhi n = π := by
  unfold threeClusterPhi
  have h : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem threeClusterPhi_lt_half_pi {n : ℕ} (hn : 2 ≤ n) : threeClusterPhi n < π / 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul := threeClusterPhi_mul n
  have hpos := threeClusterPhi_pos n
  nlinarith

theorem threeClusterPhi_cos_pos {n : ℕ} (hn : 2 ≤ n) : 0 < cos (threeClusterPhi n) :=
  cos_pos_of_mem_Ioo ⟨by linarith [threeClusterPhi_pos n, pi_pos], threeClusterPhi_lt_half_pi hn⟩

def threeClusterCenters (n : ℕ) : Fin 3 → Point :=
  ![!₂[-1, 0], !₂[1, 0], !₂[0, tan (threeClusterPhi n)]]

def threeClusterDims (n : ℕ) : Fin 3 → ℕ := ![n - 1, n - 1, n - 2]

def threeClusterOffset : Fin 3 → ℝ := ![3, 2, 3]

def threeClusterDirections (n : ℕ) (i : Fin 3) (j : Fin (threeClusterDims n i)) : Point :=
  circleDirection ((2 * (j : ℝ) + threeClusterOffset i) * threeClusterPhi n)

theorem threeClusterCenters_injective (n : ℕ) : Function.Injective (threeClusterCenters n) := by
  intro i j h
  have h0 := congrArg (fun p : Point => p 0) h
  fin_cases i <;> (try fin_cases j) <;> norm_num [threeClusterCenters] at *

theorem threeClusterDirections_ne_zero (n : ℕ) (i : Fin 3)
    (j : Fin (threeClusterDims n i)) : threeClusterDirections n i j ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [threeClusterDirections, norm_circleDirection]
  norm_num

theorem three_center_sub_10 (n : ℕ) :
    threeClusterCenters n 1 - threeClusterCenters n 0 = (2 : ℝ) • circleDirection 0 := by
  ext i
  fin_cases i <;> norm_num [threeClusterCenters, circleDirection]

theorem three_center_sub_20 {n : ℕ} (hn : 2 ≤ n) :
    threeClusterCenters n 2 - threeClusterCenters n 0 =
      (1 / cos (threeClusterPhi n)) • circleDirection (threeClusterPhi n) := by
  have hc : cos (threeClusterPhi n) ≠ 0 := ne_of_gt (threeClusterPhi_cos_pos hn)
  ext i
  fin_cases i <;> simp [threeClusterCenters, circleDirection, tan_eq_sin_div_cos, hc, div_eq_mul_inv, mul_comm]

theorem three_center_sub_21 {n : ℕ} (hn : 2 ≤ n) :
    threeClusterCenters n 2 - threeClusterCenters n 1 =
      (1 / cos (threeClusterPhi n)) • circleDirection (π - threeClusterPhi n) := by
  have hc : cos (threeClusterPhi n) ≠ 0 := ne_of_gt (threeClusterPhi_cos_pos hn)
  ext i
  fin_cases i <;> simp [threeClusterCenters, circleDirection, tan_eq_sin_div_cos, hc, div_eq_mul_inv, mul_comm]

theorem threeClusterArgument_bounds {n : ℕ} (hn : 2 ≤ n) (i : Fin 3)
    (j : Fin (threeClusterDims n i)) :
    (![3, 2, 3] : Fin 3 → ℝ) i * threeClusterPhi n ≤
        (2 * (j : ℝ) + threeClusterOffset i) * threeClusterPhi n ∧
    (2 * (j : ℝ) + threeClusterOffset i) * threeClusterPhi n ≤
      π - (![2, 3, 4] : Fin 3 → ℝ) i * threeClusterPhi n := by
  have hpos := threeClusterPhi_pos n
  have hmul := threeClusterPhi_mul n
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  fin_cases i
  · have hjNat : (j : ℕ) + 2 ≤ n := by
      have hh := j.isLt
      simp [threeClusterDims] at hh
      omega
    have hj : (j : ℝ) + 2 ≤ n := by exact_mod_cast hjNat
    norm_num [threeClusterOffset]
    constructor <;> nlinarith
  · have hjNat : (j : ℕ) + 2 ≤ n := by
      have hh := j.isLt
      simp [threeClusterDims] at hh
      omega
    have hj : (j : ℝ) + 2 ≤ n := by exact_mod_cast hjNat
    norm_num [threeClusterOffset]
    constructor <;> nlinarith
  · have hjNat : (j : ℕ) + 3 ≤ n := by
      have hh := j.isLt
      simp [threeClusterDims] at hh
      omega
    have hj : (j : ℝ) + 3 ≤ n := by exact_mod_cast hjNat
    norm_num [threeClusterOffset]
    constructor <;> nlinarith

theorem threeClusterArgument_coarse_bounds {n : ℕ} (hn : 2 ≤ n) (i : Fin 3)
    (j : Fin (threeClusterDims n i)) :
    2 * threeClusterPhi n ≤ (2 * (j : ℝ) + threeClusterOffset i) * threeClusterPhi n ∧
      (2 * (j : ℝ) + threeClusterOffset i) * threeClusterPhi n ≤ π - 2 * threeClusterPhi n := by
  have hh := threeClusterArgument_bounds hn i j
  have hpos := threeClusterPhi_pos n
  fin_cases i <;> norm_num [threeClusterOffset] at hh ⊢ <;> constructor <;> linarith

theorem threeClusterDirections_internal {n : ℕ} (hn : 2 ≤ n) (i : Fin 3)
    (p q : Fin (threeClusterDims n i)) (hpq : p ≠ q) (r s : ℝ)
    (hr : r = -1 ∨ r = 1) (hs : s = -1 ∨ s = 1) :
    InnerProductGeometry.angle (r • threeClusterDirections n i p) (s • threeClusterDirections n i q) ≤
      π - 2 * threeClusterPhi n := by
  have hpos := threeClusterPhi_pos n
  have hp := threeClusterArgument_coarse_bounds hn i p
  have hq := threeClusterArgument_coarse_bounds hn i q
  have hgap : (1 : ℝ) ≤ |(p : ℝ) - q| := by
    have hv : (p : ℕ) ≠ q := fun h => hpq (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hpq | hqp
    · have hh : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
      rw [abs_of_nonpos (by linarith : (p : ℝ) - q ≤ 0)]
      linarith
    · have hh : (q : ℝ) + 1 ≤ p := by exact_mod_cast hqp
      rw [abs_of_nonneg (by linarith : 0 ≤ (p : ℝ) - q)]
      linarith
  apply signed_circleDirection_angle_le_of_separation (by positivity) ?_ ?_ r s hr hs
  · have heq :
        |(2 * (p : ℝ) + threeClusterOffset i) * threeClusterPhi n -
          (2 * (q : ℝ) + threeClusterOffset i) * threeClusterPhi n| =
          2 * |(p : ℝ) - q| * threeClusterPhi n := by
      rw [show (2 * (p : ℝ) + threeClusterOffset i) * threeClusterPhi n -
          (2 * (q : ℝ) + threeClusterOffset i) * threeClusterPhi n =
          2 * ((p : ℝ) - q) * threeClusterPhi n by ring,
        abs_mul, abs_mul, abs_of_pos hpos]
      norm_num
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hgap hpos.le]
  · exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem three_center_angle_A {n : ℕ} (hn : 2 ≤ n) :
    EuclideanGeometry.angle (threeClusterCenters n 1) (threeClusterCenters n 0)
      (threeClusterCenters n 2) = threeClusterPhi n := by
  have hp := threeClusterPhi_pos n
  have hh := threeClusterPhi_lt_half_pi hn
  have hscale : 0 < 1 / cos (threeClusterPhi n) := by
    exact one_div_pos.mpr (threeClusterPhi_cos_pos hn)
  change InnerProductGeometry.angle
    (threeClusterCenters n 1 - threeClusterCenters n 0)
    (threeClusterCenters n 2 - threeClusterCenters n 0) = _
  rw [three_center_sub_10, three_center_sub_20 hn,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (by norm_num : (0 : ℝ) < 2),
    InnerProductGeometry.angle_smul_right_of_pos _ _ hscale,
    angle_circleDirection, zero_sub, cos_neg, arccos_cos hp.le (by linarith)]

theorem three_center_angle_B {n : ℕ} (hn : 2 ≤ n) :
    EuclideanGeometry.angle (threeClusterCenters n 0) (threeClusterCenters n 1)
      (threeClusterCenters n 2) = threeClusterPhi n := by
  have hp := threeClusterPhi_pos n
  have hh := threeClusterPhi_lt_half_pi hn
  have hscale : 0 < 1 / cos (threeClusterPhi n) :=
    one_div_pos.mpr (threeClusterPhi_cos_pos hn)
  change InnerProductGeometry.angle
    (threeClusterCenters n 0 - threeClusterCenters n 1)
    (threeClusterCenters n 2 - threeClusterCenters n 1) = _
  rw [show threeClusterCenters n 0 - threeClusterCenters n 1 =
      -(threeClusterCenters n 1 - threeClusterCenters n 0) by abel,
    three_center_sub_10, three_center_sub_21 hn,
    InnerProductGeometry.angle_neg_left,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (by norm_num : (0 : ℝ) < 2),
    InnerProductGeometry.angle_smul_right_of_pos _ _ hscale,
    angle_circleDirection, zero_sub, cos_neg,
    arccos_cos (by linarith) (by linarith)]
  ring

theorem three_center_angle_C {n : ℕ} (hn : 2 ≤ n) :
    EuclideanGeometry.angle (threeClusterCenters n 0) (threeClusterCenters n 2)
      (threeClusterCenters n 1) = π - 2 * threeClusterPhi n := by
  have hp := threeClusterPhi_pos n
  have hh := threeClusterPhi_lt_half_pi hn
  have hscale : 0 < 1 / cos (threeClusterPhi n) :=
    one_div_pos.mpr (threeClusterPhi_cos_pos hn)
  change InnerProductGeometry.angle
    (threeClusterCenters n 0 - threeClusterCenters n 2)
    (threeClusterCenters n 1 - threeClusterCenters n 2) = _
  rw [show threeClusterCenters n 0 - threeClusterCenters n 2 =
      -(threeClusterCenters n 2 - threeClusterCenters n 0) by abel,
    show threeClusterCenters n 1 - threeClusterCenters n 2 =
      -(threeClusterCenters n 2 - threeClusterCenters n 1) by abel,
    InnerProductGeometry.angle_neg_neg, three_center_sub_20 hn, three_center_sub_21 hn,
    InnerProductGeometry.angle_smul_left_of_pos _ _ hscale,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hscale,
    angle_circleDirection]
  rw [show threeClusterPhi n - (π - threeClusterPhi n) = -(π - 2 * threeClusterPhi n) by ring,
    cos_neg, arccos_cos (by linarith) (by linarith)]

theorem threeClusterCenters_angle_le {n : ℕ} (hn : 2 ≤ n) (i j k : Fin 3)
    (hij : i ≠ j) (hkj : k ≠ j) :
    EuclideanGeometry.angle (threeClusterCenters n i) (threeClusterCenters n j)
      (threeClusterCenters n k) ≤ π - 2 * threeClusterPhi n := by
  have hp := threeClusterPhi_pos n
  have hmul := threeClusterPhi_mul n
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : threeClusterPhi n ≤ π - 2 * threeClusterPhi n := by nlinarith
  by_cases hik : i = k
  · subst k
    rw [EuclideanGeometry.angle_self_of_ne ((threeClusterCenters_injective n).ne hij)]
    linarith
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num at *
  all_goals first
    | rw [three_center_angle_A hn]; exact hh
    | rw [three_center_angle_B hn]; exact hh
    | rw [three_center_angle_C hn]
    | rw [EuclideanGeometry.angle_comm, three_center_angle_A hn]; exact hh
    | rw [EuclideanGeometry.angle_comm, three_center_angle_B hn]; exact hh
    | rw [EuclideanGeometry.angle_comm, three_center_angle_C hn]

def threeCenterLineAngle (n : ℕ) : Fin 3 → Fin 3 → ℝ :=
  ![![0, 0, threeClusterPhi n], ![0, 0, π - threeClusterPhi n],
    ![threeClusterPhi n, π - threeClusterPhi n, 0]]

theorem threeCluster_direction_center_separation {n : ℕ} (hn : 2 ≤ n) (i k : Fin 3)
    (hik : i ≠ k) (p : Fin (threeClusterDims n i)) :
    2 * threeClusterPhi n ≤
        |(2 * (p : ℝ) + threeClusterOffset i) * threeClusterPhi n - threeCenterLineAngle n i k| ∧
    |(2 * (p : ℝ) + threeClusterOffset i) * threeClusterPhi n - threeCenterLineAngle n i k| ≤
      π - 2 * threeClusterPhi n := by
  have hb := threeClusterArgument_bounds hn i p
  have hp := threeClusterPhi_pos n
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  fin_cases i <;> fin_cases k <;> norm_num [threeCenterLineAngle, threeClusterOffset] at *
  all_goals simp only [abs_of_pos hp]
  all_goals constructor
  all_goals first
    | rw [abs_of_nonneg (by nlinarith)]; nlinarith
    | rw [abs_of_nonpos (by nlinarith)]; nlinarith

/-- Every center-to-center vector is a positive multiple of one signed line direction. -/
theorem threeCenter_difference_direction {n : ℕ} (hn : 2 ≤ n) (i k : Fin 3) (hik : i ≠ k) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ (σ = -1 ∨ σ = 1) ∧
      threeClusterCenters n k - threeClusterCenters n i =
        ρ • (σ • circleDirection (threeCenterLineAngle n i k)) := by
  have hscale : 0 < 1 / cos (threeClusterPhi n) :=
    one_div_pos.mpr (threeClusterPhi_cos_pos hn)
  fin_cases i <;> fin_cases k <;> norm_num at hik
  · refine ⟨2, 1, by norm_num, by simp, ?_⟩
    simpa [threeCenterLineAngle] using three_center_sub_10 n
  · refine ⟨1 / cos (threeClusterPhi n), 1, hscale, by simp, ?_⟩
    simpa [threeCenterLineAngle] using three_center_sub_20 hn
  · refine ⟨2, -1, by norm_num, by simp, ?_⟩
    simpa [threeCenterLineAngle, neg_sub] using congrArg (fun z : Point => -z) (three_center_sub_10 n)
  · refine ⟨1 / cos (threeClusterPhi n), 1, hscale, by simp, ?_⟩
    simpa [threeCenterLineAngle] using three_center_sub_21 hn
  · refine ⟨1 / cos (threeClusterPhi n), -1, hscale, by simp, ?_⟩
    simpa [threeCenterLineAngle, neg_sub] using congrArg (fun z : Point => -z) (three_center_sub_20 hn)
  · refine ⟨1 / cos (threeClusterPhi n), -1, hscale, by simp, ?_⟩
    simpa [threeCenterLineAngle, neg_sub] using congrArg (fun z : Point => -z) (three_center_sub_21 hn)

theorem threeClusterDirections_cross {n : ℕ} (hn : 2 ≤ n) (i k : Fin 3) (hik : i ≠ k)
    (p : Fin (threeClusterDims n i)) (r : ℝ) (hr : r = -1 ∨ r = 1) :
    InnerProductGeometry.angle (r • threeClusterDirections n i p)
      (threeClusterCenters n k - threeClusterCenters n i) ≤ π - 2 * threeClusterPhi n := by
  obtain ⟨ρ, σ, hρ, hσ, heq⟩ := threeCenter_difference_direction hn i k hik
  rw [heq, InnerProductGeometry.angle_smul_right_of_pos _ _ hρ]
  obtain ⟨hlo, hhi⟩ := threeCluster_direction_center_separation hn i k hik p
  exact signed_circleDirection_angle_le_of_separation
    (mul_nonneg (by norm_num) (threeClusterPhi_pos n).le) hlo hhi r σ hr hσ

theorem threeCluster_cardinality {n : ℕ} (hn : 2 ≤ n) :
    (∑ i : Fin 3, 2 ^ threeClusterDims n i) = 5 * 2 ^ (n - 2) := by
  norm_num [Fin.sum_univ_succ, threeClusterDims]
  have heq : n - 1 = (n - 2) + 1 := by omega
  simp only [heq, pow_succ]
  ring

/-- The explicit three-center, binary-cluster construction gives the improved upper bound. -/
theorem sendov_intermediate_upper_bound (n : ℕ) (hn : 2 ≤ n) :
    alpha (5 * 2 ^ (n - 2)) ≤ (1 - 2 / (2 * (n : ℝ) + 1)) * π := by
  have hh := threeClusterPhi_lt_half_pi hn
  have hsize : 3 ≤ ∑ i : Fin 3, 2 ^ threeClusterDims n i := by
    rw [threeCluster_cardinality hn]
    have hpos : 0 < 2 ^ (n - 2) := pow_pos (by norm_num) _
    omega
  have hbound := alpha_sum_two_pow_le_of_cluster_directions
    (threeClusterCenters n) (threeClusterCenters_injective n)
    (threeClusterDirections n) (threeClusterDirections_ne_zero n)
    (by linarith : 0 ≤ π - 2 * threeClusterPhi n) hsize
    (threeClusterCenters_angle_le hn) (threeClusterDirections_internal hn)
    (threeClusterDirections_cross hn)
  rw [threeCluster_cardinality hn] at hbound
  convert hbound using 1
  unfold threeClusterPhi
  ring

theorem alpha_le_sendov_intermediate_upper {N n : ℕ} (hn : 2 ≤ n) (hN : 3 ≤ N)
    (hsize : N ≤ 5 * 2 ^ (n - 2)) :
    alpha N ≤ (1 - 2 / (2 * (n : ℝ) + 1)) * π :=
  (alpha_mono hN hsize).trans (sendov_intermediate_upper_bound n hn)

theorem alpha_five_le_three_pi_div_five : alpha 5 ≤ 3 * π / 5 := by
  have hh := sendov_intermediate_upper_bound 2 (by norm_num)
  norm_num at hh
  linarith

/-- The cluster cardinality equals the cutoff written in Sendov's theorem. -/
theorem threeCluster_cutoff_eq_source {n : ℕ} (hn : 2 ≤ n) :
    5 * 2 ^ (n - 2) = 2 ^ n + 2 ^ (n - 2) := by
  have hn' : n = (n - 2) + 2 := by omega
  have hp : 2 ^ n = 4 * 2 ^ (n - 2) := by
    calc
      2 ^ n = 2 ^ ((n - 2) + 2) := congrArg (fun k : ℕ => 2 ^ k) hn'
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; norm_num; ring
  rw [hp]
  ring

/-- Both intervals of Sendov's classification formula are unconditional upper bounds. -/
theorem sendov_piecewise_upper_bound {n N : ℕ} (hn : 2 ≤ n)
    (hlo : 2 ^ n < N) (hhi : N ≤ 2 ^ (n + 1)) :
    alpha N ≤ if N ≤ 2 ^ n + 2 ^ (n - 2) then
      (1 - 2 / (2 * (n : ℝ) + 1)) * π
    else
      (1 - 1 / ((n + 1 : ℕ) : ℝ)) * π := by
  have hN : 3 ≤ N := (three_le_two_pow hn).trans hlo.le
  rw [← threeCluster_cutoff_eq_source hn]
  by_cases hmid : N ≤ 5 * 2 ^ (n - 2)
  · rw [ite_eq_left hmid]
    exact alpha_le_sendov_intermediate_upper hn hN hmid
  · rw [ite_eq_right hmid]
    exact alpha_le_szekeres_upper hN (by omega) hhi

end JSP404
