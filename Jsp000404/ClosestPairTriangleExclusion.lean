import Jsp000404.SaturatedNesting
import Jsp000404.TwoSaturatedFour
import Mathlib.Data.Fintype.Lattice
import Mathlib.Geometry.Euclidean.Triangle

/-! A genuine finite metric extraction for higher-strip actual configurations.
A closest pair cannot be the base of a triangle containing another actual
center when lambda > pi/6. This excludes interior blockers only. It does not
assert projective fan adjacency, a legal pair collapse, or a capacity bound.
-/

open scoped EuclideanGeometry

namespace Jsp404.ClosestPairTriangleExclusion

/-- The minimum is over actual distances of all distinct index pairs. -/
def IsClosestPair {s : ℕ} (c : Fin s → Plane₂) (p q : Fin s) : Prop :=
  p ≠ q ∧ ∀ i j : Fin s, i ≠ j → dist (c p) (c q) ≤ dist (c i) (c j)

/-- The closest pair is chosen internally from the finite family. -/
theorem exists_closest_pair {s : ℕ} (hs : 2 ≤ s) (c : Fin s → Plane₂) :
    ∃ p q : Fin s, IsClosestPair c p q := by
  classical
  let P := {z : Fin s × Fin s // z.1 ≠ z.2}
  let zero : Fin s := ⟨0, by omega⟩
  let one : Fin s := ⟨1, by omega⟩
  have hzeroone : zero ≠ one := by
    intro h
    have := congrArg Fin.val h
    norm_num [zero, one] at this
  let : Nonempty P := ⟨⟨(zero, one), hzeroone⟩⟩
  obtain ⟨z, hz⟩ := Finite.exists_min (fun z : P => dist (c z.1.1) (c z.1.2))
  exact ⟨z.1.1, z.1.2, z.2, fun i j hij => hz ⟨(i,j), hij⟩⟩

/-- The angle opposite a globally shortest side is at most pi/3. -/
theorem closest_pair_angle_le_pi_div_three {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hleg : Section4Legality c lam) {p q r : Fin s}
    (hpq : IsClosestPair c p q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∠ (c p) (c r) (c q) ≤ Real.pi / 3 := by
  have hq : ∠ (c p) (c r) (c q) ≤ ∠ (c p) (c q) (c r) :=
    (EuclideanGeometry.angle_le_iff_dist_le
      (legal_triple_not_collinear hleg hpq.1 hpr hqr)).mpr (hpq.2 p r hpr)
  have hp : ∠ (c q) (c r) (c p) ≤ ∠ (c q) (c p) (c r) :=
    (EuclideanGeometry.angle_le_iff_dist_le
      (legal_triple_not_collinear hleg hpq.1.symm hqr hpr)).mpr
        (by simpa only [dist_comm] using hpq.2 q r hqr)
  rw [EuclideanGeometry.angle_comm (c q) (c r) (c p)] at hp
  apply EuclideanGeometry.angle_le_pi_div_three_of_le_of_le
  · simpa only [EuclideanGeometry.angle_comm (c r) (c q) (c p)] using hq
  · exact hp
  · exact Or.inl (hleg.inj.ne hpr)

/-- No fourth center lies in the triangle with the closest pair as its base.
Legality excludes collinear boundary cases; actual strict betweenness gives
the angle sum at an interior center, rather than an assumed circle order. -/
theorem closest_pair_triangle_empty {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlarge : Real.pi / 6 < lam)
    {p q x r : Fin s} (hpq : IsClosestPair c p q)
    (hpx : p ≠ x) (hqx : q ≠ x)
    (hrp : r ≠ p) (hrq : r ≠ q) (hrx : r ≠ x) :
    c r ∉ convexHull ℝ ({c p, c q, c x} : Set Plane₂) := by
  intro hmem
  obtain ⟨E, hE, hr⟩ := strict_nested_of_mem_convexHull hmem (hleg.inj.ne hrx)
    (legal_triple_not_collinear hleg hrx.symm hpx.symm hrp)
    (legal_triple_not_collinear hleg hrx.symm hqx.symm hrq)
    (legal_triple_not_collinear hleg hrp.symm hpq.1 hrq)
  have hsum := angle_sum_eq_two_pi_of_nested hE hr
  have hcapP := hleg.triAngle p r x hrp.symm hrx hpx
  have hcapQ := hleg.triAngle q r x hrq.symm hrx hqx
  have hsmall := closest_pair_angle_le_pi_div_three hleg hpq hrp.symm hrq.symm
  linarith

/-- A legal configuration above pi/6 internally supplies a closest pair
whose triangle with every third center is free of every fourth center. -/
theorem exists_closest_pair_with_empty_triangles {s : ℕ} (hs : 3 ≤ s)
    (c : Fin s → Plane₂) {lam : ℝ} (hleg : Section4Legality c lam)
    (hlarge : Real.pi / 6 < lam) :
    ∃ p q : Fin s, IsClosestPair c p q ∧
      ∀ x r : Fin s, p ≠ x → q ≠ x → r ≠ p → r ≠ q → r ≠ x →
        c r ∉ convexHull ℝ ({c p, c q, c x} : Set Plane₂) := by
  obtain ⟨p, q, hpq⟩ := exists_closest_pair (by omega : 2 ≤ s) c
  exact ⟨p, q, hpq, fun _ _ hpx hqx hrp hrq hrx =>
    closest_pair_triangle_empty hleg hlarge hpq hpx hqx hrp hrq hrx⟩

#print axioms exists_closest_pair
#print axioms closest_pair_angle_le_pi_div_three
#print axioms closest_pair_triangle_empty
#print axioms exists_closest_pair_with_empty_triangles

end Jsp404.ClosestPairTriangleExclusion
