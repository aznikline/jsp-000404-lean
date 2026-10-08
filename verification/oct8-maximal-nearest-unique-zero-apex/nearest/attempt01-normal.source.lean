import Jsp000404.ActualMaximalLowClumpWeight
import Jsp000404.SharpNearestGeometry

/-! SOURCE_ONLY actual closer witnesses for maximal nonacute LOW rows.

The original target q is arbitrary and may be an internal or boundary ray
of either actual clump. Only noncentral rays are used in the angle lemmas.
The actual zero gain and clump geometry are supplied internally by verified
general producers. No nearest map, clump, angle-gap budget or capacity
conclusion is a caller premise. This candidate has not been compiled.
-/

set_option autoImplicit false
set_option pp.fullNames true
open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.GeneralMaximalNonacuteNotNearest

/-- Every distinct original target has a genuinely closer original point
than this maximal nonacute center. LOW keeps its strict lower endpoint and
closed upper endpoint; the nonacute witness may be exactly2lambda. -/
theorem actual_maximal_nonacute_has_closer_witness {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = n - 2)
    (hwide : ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b))
    (q : Fin s) (hpq : p ≠ q) :
    ∃ r : Fin s, r ≠ p ∧ r ≠ q ∧ dist (c q) (c r) < dist (c q) (c p) := by
  have hzero := ActualMaximalLowClumpWeight.actual_maximal_observer_gain_eq_zero
    hn4 o e he H p hp q hpq
  obtain ⟨r, hrp, hrq, hsmall⟩ :=
    (emit_or_near_collinear o e c H.legality he hpq H.card_ge_three).resolve_left (by
      intro hgain
      rw [hzero] at hgain
      omega)
  obtain ⟨D⟩ := ActualMaximalLowClumpWeight.exists_actual_maximal_low_clump_weight
    hn4 o e he H p hp hwide
  have hsame : D.geometry.clumps.code q = D.geometry.clumps.code r := by
    by_contra hdiff
    have hlarge := D.geometry.clumps.different_angle_ge H.legality
      q r hpq.symm hrp hdiff
    linarith [H.legality.lam_pos]
  have hbound := D.geometry.clumps.same_angle_le H.legality q r hpq.symm hrp hsame
  have hhalf : ∠ (c q) (c p) (c r) < lam / 2 :=
    hbound.trans_lt D.geometry.remainder_lt_half
  have hcloser := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
    H.legality hpq hrp.symm hrq.symm hhalf
  exact ⟨r, hrp, hrq, hcloser⟩

#print axioms actual_maximal_nonacute_has_closer_witness

end Jsp404.GeneralMaximalNonacuteNotNearest
