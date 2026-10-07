import Jsp000404.SharpNearestGeometry
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

/-! A score-free actual geometry core for three narrow two-cluster centers.
Every angle in the hypotheses is computed from actual original points.
The one-small-angle branch uses a proved factor-two side comparison;
it does not infer an unlicensed half-scale angle at the companion.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.SmallTwoClusterGeometry

/-- Explicit physical two-cluster data for a geometric helper. Actual
model consumers must construct this data from their original producers. -/
structure TwoClusters {s : ℕ} (c : Fin s → Plane₂) (lam R : ℝ) (p : Fin s) where
  code : Fin s → Bool
  same_angle : ∀ i j, i ≠ p → j ≠ p → code i = code j →
    ∠ (c i) (c p) (c j) ≤ R
  different_angle : ∀ i j, i ≠ p → j ≠ p → code i ≠ code j →
    2*lam ≤ ∠ (c i) (c p) (c j)
  companion : ∀ q, q ≠ p → ∃ r, r ≠ p ∧ r ≠ q ∧ code r = code q

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (A B C : Fin s) (hAB : A ≠ B) :
    ∠ (c B) (c A) (c C) + ∠ (c A) (c B) (c C) +
      ∠ (c A) (c C) (c B) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c A) (p₂ := c B) (c C) (hleg.inj.ne hAB.symm)
  rw [EuclideanGeometry.angle_comm (c B) (c C) (c A),
    EuclideanGeometry.angle_comm (c C) (c A) (c B)] at hsum
  linarith

private theorem two_small_false {s : ℕ} {c : Fin s → Plane₂} {lam R : ℝ}
    (hleg : Section4Legality c lam) (hR : R < lam/2)
    (A B C : Fin s) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA : ∠ (c B) (c A) (c C) ≤ R)
    (hB : ∠ (c A) (c B) (c C) ≤ R) : False := by
  have hsum := actual_triangle_sum hleg A B C hAB
  have hcap := hleg.triAngle A C B hAC hBC.symm hAB
  linarith

private theorem bool_eq_of_two_ne {a b d : Bool} (hab : a ≠ b) (hbd : b ≠ d) : a = d := by
  cases a <;> cases b <;> cases d <;> simp_all

private theorem sine_more_than_twice {a b d : ℝ}
    (ha : 0 < a) (hsum : a+b+d = Real.pi) (hb : 4*a < b) (hd : 4*a < d) :
    2*Real.sin a < Real.sin b := by
  have hx : 0 ≤ 4*a := by linarith
  have hxpi : 4*a ≤ Real.pi/2 := by linarith
  have hother : 4*a ≤ Real.pi-b := by linarith
  have hsin4 : Real.sin (4*a) ≤ Real.sin b := by
    by_cases hbhalf : b ≤ Real.pi/2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hbhalf hb.le
    · have hbgt : Real.pi/2 < b := lt_of_not_ge hbhalf
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos] : -(Real.pi/2) ≤ 4*a)
        (by linarith : Real.pi-b ≤ Real.pi/2) hother
      simpa only [Real.sin_pi_sub] using h
  have hjordan := Real.mul_le_sin hx hxpi
  have hcoef : (2 : ℝ) < 8/Real.pi :=
    (lt_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
  have hlinear : 2*a < (2/Real.pi)*(4*a) := by
    calc
      2*a < (8/Real.pi)*a := mul_lt_mul_of_pos_right hcoef ha
      _ = (2/Real.pi)*(4*a) := by ring
  have hsina := Real.sin_le ha.le
  calc
    2*Real.sin a ≤ 2*a := mul_le_mul_of_nonneg_left hsina (by norm_num)
    _ < (2/Real.pi)*(4*a) := hlinear
    _ ≤ Real.sin (4*a) := hjordan
    _ ≤ Real.sin b := hsin4

/-- A genuine triangle with one angle below half the legal scale and
both other angles at least twice that scale has side AC longer than
2*BC. The sine rule is applied to these actual points internally. -/
theorem twice_base_lt_side_of_small_apex {s : ℕ} {c : Fin s → Plane₂} {lam R : ℝ}
    (hleg : Section4Legality c lam) (hR : R < lam/2)
    (A B C : Fin s) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA : ∠ (c B) (c A) (c C) ≤ R)
    (hB : 2*lam ≤ ∠ (c A) (c B) (c C))
    (hC : 2*lam ≤ ∠ (c A) (c C) (c B)) :
    2*dist (c B) (c C) < dist (c A) (c C) := by
  have hnc := legal_triple_not_collinear hleg hAB.symm hBC hAC
  have hapos := EuclideanGeometry.angle_pos_of_not_collinear hnc
  have hsum := actual_triangle_sum hleg A B C hAB
  have hsin := sine_more_than_twice hapos hsum
    (by linarith : 4 * (∠ (c B) (c A) (c C)) < ∠ (c A) (c B) (c C))
    (by linarith : 4 * (∠ (c B) (c A) (c C)) < ∠ (c A) (c C) (c B))
  have hlaw := EuclideanGeometry.law_sin (c A) (c B) (c C)
  rw [EuclideanGeometry.angle_comm (c C) (c A) (c B),
    dist_comm (c C) (c A)] at hlaw
  have hbase : 0 < dist (c B) (c C) := dist_pos.mpr (hleg.inj.ne hBC)
  have hsinapos : 0 < Real.sin (∠ (c B) (c A) (c C)) :=
    EuclideanGeometry.sin_pos_of_not_collinear hnc
  by_contra hnot
  have hlen : dist (c A) (c C) ≤ 2*dist (c B) (c C) := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_left hlen hsinapos.le
  have hstrict := mul_lt_mul_of_pos_right hsin hbase
  nlinarith

private theorem one_small_false {s : ℕ} {c : Fin s → Plane₂} {lam R : ℝ}
    (hleg : Section4Legality c lam) (hR : R < lam/2)
    (A B C : Fin s) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (DB : TwoClusters c lam R B) (DC : TwoClusters c lam R C)
    (hsmallA : ∠ (c B) (c A) (c C) ≤ R) : False := by
  have hsmallA' : ∠ (c C) (c A) (c B) ≤ R := by
    rw [EuclideanGeometry.angle_comm (c C) (c A) (c B)]
    exact hsmallA
  have hBAC : DB.code A ≠ DB.code C := by
    intro h
    exact two_small_false hleg hR A B C hAB hAC hBC hsmallA
      (DB.same_angle A C hAB hBC.symm h)
  have hCAB : DC.code A ≠ DC.code B := by
    intro h
    exact two_small_false hleg hR A C B hAC hAB hBC.symm hsmallA'
      (DC.same_angle A B hAC hBC h)
  have hlargeB := DB.different_angle A C hAB hBC.symm hBAC
  have hlargeC := DC.different_angle A B hAC hBC hCAB
  have hfactor := twice_base_lt_side_of_small_apex hleg hR A B C hAB hAC hBC
    hsmallA hlargeB hlargeC
  obtain ⟨u,huB,huC,hBuC⟩ := DB.companion C hBC.symm
  have huA : u ≠ A := by
    intro h
    apply hBAC
    simpa only [h] using hBuC
  have hsmallB : ∠ (c C) (c B) (c u) ≤ R :=
    DB.same_angle C u hBC.symm huB hBuC.symm
  have hCBu : DC.code B ≠ DC.code u := by
    intro h
    have hsmallC := DC.same_angle B u hBC huC h
    exact two_small_false hleg hR B C u hBC huB.symm huC.symm hsmallB hsmallC
  have hCAu : DC.code A = DC.code u := bool_eq_of_two_ne hCAB hCBu
  have hsmallC : ∠ (c u) (c C) (c A) ≤ R :=
    DC.same_angle u A huC hAC hCAu.symm
  have h1 := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
    hleg hBC huB.symm huC.symm (hsmallB.trans_lt hR)
  have h2 := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
    hleg huC.symm hAC.symm huA (hsmallC.trans_lt hR)
  rw [dist_comm (c C) (c B)] at h1
  rw [dist_comm (c u) (c A),dist_comm (c u) (c C)] at h2
  have htri := dist_triangle (c A) (c u) (c C)
  rw [dist_comm (c u) (c C)] at htri
  linarith

private theorem no_small_false {s : ℕ} {c : Fin s → Plane₂} {lam R : ℝ}
    (hleg : Section4Legality c lam) (hR : R < lam/2)
    (A B C : Fin s) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (DA : TwoClusters c lam R A) (DB : TwoClusters c lam R B) (DC : TwoClusters c lam R C)
    (hA : DA.code B ≠ DA.code C) (hB : DB.code A ≠ DB.code C)
    (hC : DC.code A ≠ DC.code B) : False := by
  obtain ⟨u,huA,huB,hAuB⟩ := DA.companion B hAB.symm
  have huC : u ≠ C := by
    intro h
    apply hA
    simpa only [h] using hAuB.symm
  have hsmallA : ∠ (c B) (c A) (c u) ≤ R :=
    DA.same_angle B u hAB.symm huA hAuB.symm
  have hBAu : DB.code A ≠ DB.code u := by
    intro h
    have hsmallB := DB.same_angle A u hAB huB h
    exact two_small_false hleg hR A B u hAB huA.symm huB.symm hsmallA hsmallB
  have hBuC : DB.code u = DB.code C := bool_eq_of_two_ne (Ne.symm hBAu) hB
  have hsmallB : ∠ (c C) (c B) (c u) ≤ R :=
    DB.same_angle C u hBC.symm huB hBuC.symm
  have hCBu : DC.code B ≠ DC.code u := by
    intro h
    have hsmallC := DC.same_angle B u hBC huC h
    exact two_small_false hleg hR B C u hBC huB.symm huC.symm hsmallB hsmallC
  have hCAu : DC.code A = DC.code u := bool_eq_of_two_ne hC hCBu
  have h1 := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
    hleg huA.symm hAB huB
    ((DA.same_angle u B huA hAB.symm hAuB).trans_lt hR)
  have h2 := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
    hleg huB.symm hBC huC
    ((DB.same_angle u C huB hBC.symm hBuC).trans_lt hR)
  have h3 := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
    hleg huC.symm hAC.symm huA
    ((DC.same_angle u A huC hAC hCAu.symm).trans_lt hR)
  linarith

/-- Three injectively selected actual centers cannot all have these
physical narrow two-cluster data and same-cluster companions. The only
scale condition is R<lambda/2; lambda positivity is actual legality. -/
theorem no_three_small_two_clusters {s : ℕ} {c : Fin s → Plane₂} {lam R : ℝ}
    (hleg : Section4Legality c lam) (hR : R < lam/2)
    (pick : Fin 3 → Fin s) (hpick : Function.Injective pick)
    (D : ∀ i : Fin 3, TwoClusters c lam R (pick i)) : False := by
  let A := pick 0
  let B := pick 1
  let C := pick 2
  let DA : TwoClusters c lam R A := D 0
  let DB : TwoClusters c lam R B := D 1
  let DC : TwoClusters c lam R C := D 2
  have hAB : A ≠ B := hpick.ne (by decide : (0 : Fin 3) ≠ 1)
  have hAC : A ≠ C := hpick.ne (by decide : (0 : Fin 3) ≠ 2)
  have hBC : B ≠ C := hpick.ne (by decide : (1 : Fin 3) ≠ 2)
  by_cases hA : DA.code B = DA.code C
  · exact one_small_false hleg hR A B C hAB hAC hBC DB DC
      (DA.same_angle B C hAB.symm hAC.symm hA)
  by_cases hB : DB.code A = DB.code C
  · exact one_small_false hleg hR B A C hAB.symm hBC hAC DA DC
      (DB.same_angle A C hAB hBC.symm hB)
  by_cases hC : DC.code A = DC.code B
  · exact one_small_false hleg hR C A B hAC.symm hBC.symm hAB DA DB
      (DC.same_angle A B hAC hBC hC)
  exact no_small_false hleg hR A B C hAB hAC hBC DA DB DC hA hB hC

#print axioms twice_base_lt_side_of_small_apex
#print axioms no_three_small_two_clusters

end Jsp404.SmallTwoClusterGeometry
