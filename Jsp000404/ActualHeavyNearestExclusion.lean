import Jsp000404.ActualF18HeavyZeroGain
import Jsp000404.ActualMixedRigidCardinality
import Jsp000404.SharpNearestGeometry

set_option autoImplicit false

/-! Actual nearest-neighbor exclusion for original nonacute heavy centers.
The actual zero gain and the heavy angle dichotomy are produced internally;
all original points remain available to the strict closer-point witness.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualHeavyNearestExclusion

/-- An original score-two center with an actual angle at least twice
lambda cannot be a weak nearest neighbor of any other original point.
The internally produced witness is strictly closer at the target q. -/
theorem actual_nonacute_heavy_not_weak_nearest {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (hlarge : ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b))
    (q : Fin s) (hpq : p ≠ q) :
    ¬ (∀ j : Fin s, q ≠ j → dist (c q) (c p) ≤ dist (c q) (c j)) := by
  intro hnear
  have hrho : Real.pi / ((4 : ℝ) + 1 / 2) = 2 * Real.pi / 9 := by ring
  have hlo : 2 * Real.pi / 9 < lam := by rw [← hrho]; exact H.scale_lower
  have hzero := ActualF18HeavyZeroGain.actual_low_four_heavy_observer_gain_eq_zero
    o e he H p hp q hpq
  obtain ⟨r,hrp,hrq,hsmall⟩ :=
    (emit_or_near_collinear o e c H.legality he hpq H.card_ge_three).resolve_left (by
      intro hpos
      rw [hzero] at hpos
      omega)
  have hgap := ActualMixedRigidCardinality.actual_heavy_large_angle_gap
    H.card_ge_three o e he H.legality hlo H.scale_upper p hp hlarge q r hpq.symm hrp
  have hbound : ∠ (c q) (c p) (c r) ≤ Real.pi - 4 * lam := by
    rcases hgap with hgap | hgap
    · exact hgap
    · linarith [H.legality.lam_pos]
  have hhalf : ∠ (c q) (c p) (c r) < lam / 2 := by linarith
  have hcloser := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
    H.legality hpq hrp.symm hrq.symm hhalf
  exact (not_lt_of_ge (hnear r hrq.symm)) hcloser

#print axioms actual_nonacute_heavy_not_weak_nearest

end Jsp404.ActualHeavyNearestExclusion
