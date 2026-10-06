import Jsp000404.SaturatedNesting
import Mathlib.Geometry.Euclidean.Triangle

set_option autoImplicit false

/-! Actual metric steps for the n4 LOW three-run argument.
The hypotheses and conclusions refer directly to the original points.
No direction array, deletion-score model, or capacity bound is assumed.
The three-run extraction and its application to critical models are not
proved by this file.
-/

open scoped EuclideanGeometry

namespace Jsp404.SharpNearestGeometry

/-- A ray within half the legal scale supplies a strictly nearer point
at its other endpoint. The distance comparison is at q, not at p. -/
theorem actual_third_point_closer_of_half_scale_angle {s : ℕ}
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    {p q j : Fin s} (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hsmall : ∠ (c q) (c p) (c j) < lam / 2) :
    dist (c q) (c j) < dist (c q) (c p) := by
  have hcap := hleg.triAngle p q j hpq hqj hpj
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c q) (p₂ := c p) (c j) (hleg.inj.ne hpq)
  rw [EuclideanGeometry.angle_comm (c j) (c q) (c p),
    EuclideanGeometry.angle_comm (c p) (c j) (c q)] at hsum
  have hlt : ∠ (c q) (c p) (c j) < ∠ (c q) (c j) (c p) := by
    linarith
  exact (EuclideanGeometry.angle_lt_iff_dist_lt
    (legal_triple_not_collinear hleg hqj hpq.symm hpj.symm)).mp hlt

/-- Two distinct points whose angle at a is below pi/3 cannot both have
a as a weak nearest neighbor among the actual original centers. -/
theorem actual_nearest_indices_eq_of_small_anchor_angle {s : ℕ}
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    {a u v : Fin s} (hau : a ≠ u) (hav : a ≠ v)
    (hu : ∀ j : Fin s, u ≠ j → dist (c u) (c a) ≤ dist (c u) (c j))
    (hv : ∀ j : Fin s, v ≠ j → dist (c v) (c a) ≤ dist (c v) (c j))
    (hsmall : ∠ (c u) (c a) (c v) < Real.pi / 3) : u = v := by
  by_contra huv
  have hne : u ≠ v := huv
  have hvangle : ∠ (c u) (c v) (c a) ≤ ∠ (c u) (c a) (c v) :=
    (EuclideanGeometry.angle_le_iff_dist_le
      (legal_triple_not_collinear hleg hau.symm hne hav)).mpr (hu v hne)
  have huangle : ∠ (c v) (c u) (c a) ≤ ∠ (c v) (c a) (c u) :=
    (EuclideanGeometry.angle_le_iff_dist_le
      (legal_triple_not_collinear hleg hav.symm hne.symm hau)).mpr
        (hv u hne.symm)
  rw [EuclideanGeometry.angle_comm (c v) (c a) (c u)] at huangle
  have hlarge : Real.pi / 3 ≤ ∠ (c u) (c a) (c v) :=
    EuclideanGeometry.pi_div_three_le_angle_of_le_of_le
      (by simpa only [EuclideanGeometry.angle_comm (c a) (c v) (c u)] using hvangle)
      huangle
  linarith

#print axioms actual_third_point_closer_of_half_scale_angle
#print axioms actual_nearest_indices_eq_of_small_anchor_angle

end Jsp404.SharpNearestGeometry
