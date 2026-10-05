import Jsp000404.ClosestPairTriangleExclusion
import Jsp000404.ActualMinimumCardBandMaximizer

/-! Genuine outward witnesses for zero gain along a closest pair.
No projective adjacency, legal pair collapse, or globally maximal endpoint
score is asserted. The minimum-cardinality band model supplies zero gain
from just the two endpoints' score comparison.
-/

open scoped EuclideanGeometry EuclideanSpace RealInnerProductSpace

namespace Jsp404.ClosestPairZeroGainWitness

/-- The witness contains actual unoriented triangle angles. -/
def Witness {s : ℕ} (c : Fin s → Plane₂) (lam : ℝ) (p q j : Fin s) : Prop :=
  j ≠ p ∧ j ≠ q ∧
    lam / 2 ≤ ∠ (c q) (c p) (c j) ∧ ∠ (c q) (c p) (c j) < lam ∧
    Real.pi - 2 * lam < ∠ (c p) (c q) (c j) ∧
    ∠ (c p) (c q) (c j) ≤ Real.pi - lam ∧
    ∠ (c p) (c j) (c q) ≤ ∠ (c q) (c p) (c j)

/-- Zero actual gain supplies a near ray, and the shortest-side comparison
and actual triangle sum give both endpoint bounds and the opposite angle. -/
theorem exists_witness_of_zero_gain {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    {p q : Fin s} (hpq : ClosestPairTriangleExclusion.IsClosestPair c p q)
    (hzero : rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0) :
    ∃ j : Fin s, Witness c lam p q j := by
  obtain ⟨j, hjp, hjq, hsmall⟩ :=
    (emit_or_near_collinear o e c hleg he hpq.1 hs).resolve_left (by
      intro hgain
      rw [hzero] at hgain
      omega)
  have hshort : ∠ (c q) (c j) (c p) ≤ ∠ (c q) (c p) (c j) :=
    (EuclideanGeometry.angle_le_iff_dist_le
      (legal_triple_not_collinear hleg hpq.1.symm hjq.symm hjp.symm)).mpr
        (by simpa only [dist_comm] using hpq.2 q j hjq.symm)
  rw [EuclideanGeometry.angle_comm (c q) (c j) (c p)] at hshort
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c q) (p₂ := c p) (c j) (hleg.inj.ne hpq.1)
  rw [EuclideanGeometry.angle_comm (c j) (c q) (c p)] at hsum
  have hupper := hleg.triAngle p q j hpq.1 hjq.symm hjp.symm
  exact ⟨j, hjp, hjq, by linarith, hsmall, by linarith, hupper, hshort⟩

/-- When lambda <= pi/4 the witness lies strictly beyond q's perpendicular
hyperplane, in the direction p-to-q. This is an actual positive projection. -/
theorem witness_positive_outward_projection {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} {p q j : Fin s} (hsmall : lam ≤ Real.pi / 4)
    (hw : Witness c lam p q j) :
    0 < inner ℝ (c q - c p) (c j - c q) := by
  have hang : Real.pi / 2 < ∠ (c p) (c q) (c j) := by
    have h := hw.2.2.2.2.1
    linarith
  have hneg : inner ℝ (c p - c q) (c j - c q) < 0 :=
    InnerProductGeometry.inner_neg_iff_pi_div_two_lt_angle.mpr hang
  rw [show c p - c q = -(c q - c p) by abel, inner_neg_left] at hneg
  linarith

/-- A closest pair needs only relative score order. The real minimum-card
band model's excluded CertA rules out positive gain from p to q. -/
theorem exists_witness_of_min_card_score_order {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : ActualMinimumCardBandMaximizer.Model o e rho upper M (s + 1) c lam)
    {p q : Fin (s + 1)} (hpq : ClosestPairTriangleExclusion.IsClosestPair c p q)
    (horder : rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c p)) :
    ∃ j : Fin (s + 1), Witness c lam p q j ∧
      (lam ≤ Real.pi / 4 → 0 < inner ℝ (c q - c p) (c j - c q)) := by
  have hzero : rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0 := by
    by_contra hnot
    have hg : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by omega
    have hlt := ActualMinimumCardBandMaximizer.actual_positive_gain_score_lt
      hs o e H hpq.1 hg
    omega
  obtain ⟨j, hw⟩ := exists_witness_of_zero_gain (by omega : 3 ≤ s + 1)
    o e he H.legality hpq hzero
  exact ⟨j, hw, fun hsmall => witness_positive_outward_projection hsmall hw⟩

/-- The closest pair is chosen internally and oriented from the endpoint
with larger score to the one with smaller score; ties are allowed. -/
theorem exists_oriented_closest_pair_witness {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {rho upper lam : ℝ} {M : ℕ} {c : Fin (s + 1) → Plane₂}
    (H : ActualMinimumCardBandMaximizer.Model o e rho upper M (s + 1) c lam) :
    ∃ p q j : Fin (s + 1), ClosestPairTriangleExclusion.IsClosestPair c p q ∧
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c p) ∧
      Witness c lam p q j ∧
      (lam ≤ Real.pi / 4 → 0 < inner ℝ (c q - c p) (c j - c q)) := by
  obtain ⟨p, q, hpq⟩ := ClosestPairTriangleExclusion.exists_closest_pair
    (by omega : 2 ≤ s + 1) c
  by_cases horder : rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c p)
  · obtain ⟨j, hw, hout⟩ := exists_witness_of_min_card_score_order hs o e he H hpq horder
    exact ⟨p, q, j, hpq, horder, hw, hout⟩
  · have horder' : rowScore lam (directionRow o e c p) ≤ rowScore lam (directionRow o e c q) :=
      by omega
    have hqp : ClosestPairTriangleExclusion.IsClosestPair c q p := by
      refine ⟨hpq.1.symm, ?_⟩
      intro i j hij
      rw [dist_comm (c q) (c p)]
      exact hpq.2 i j hij
    obtain ⟨j, hw, hout⟩ := exists_witness_of_min_card_score_order hs o e he H hqp horder'
    exact ⟨q, p, j, hqp, horder', hw, hout⟩

#print axioms exists_witness_of_zero_gain
#print axioms witness_positive_outward_projection
#print axioms exists_witness_of_min_card_score_order
#print axioms exists_oriented_closest_pair_witness

end Jsp404.ClosestPairZeroGainWitness
