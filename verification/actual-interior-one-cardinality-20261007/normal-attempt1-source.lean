import Jsp000404.ActualRigidCardinality
import Jsp000404.ActualInteriorOneAngleGap

/-! Actual interior score-one cardinality, with the angular condition
produced internally from the original full configuration. -/

set_option autoImplicit false
set_option pp.fullNames true
open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualInteriorOneCardinality

/-- Any selected original interior score-one points number at most four.
The actual ray gaps are taken in the original configuration, not recomputed
and silently identified after restriction. -/
theorem selected_actual_interior_one_card_le_four {s r : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick)
    (hinterior : ∀ i, ¬ IsHullVertex c (pick i))
    (hscore : ∀ i, rowScore lam (directionRow o e c (pick i)) = 1) : r ≤ 4 := by
  by_cases hr : 2 ≤ r
  · have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hleg.lam_pos.le)
    rw [hn, le_div_iff₀ hleg.lam_pos] at hfloor
    norm_num at hfloor
    have hupper : lam ≤ Real.pi / 4 := by linarith
    apply ActualRigidCardinality.card_le_four_of_actual_angle_gap hr o
      (hleg.restrict_injective pick hpick) hlo hupper
    intro i j k hij hjk _hik
    change ∠ (c (pick i)) (c (pick j)) (c (pick k)) ≤ Real.pi - 4 * lam ∨
      2 * lam ≤ ∠ (c (pick i)) (c (pick j)) (c (pick k))
    exact ActualInteriorOneAngleGap.actual_interior_one_angle_gap hs o e he hleg hlo
      (pick j) (hinterior j) (hscore j) (hpick.ne hij) (hpick.ne hjk.symm)
  · omega

#print axioms selected_actual_interior_one_card_le_four
end Jsp404.ActualInteriorOneCardinality
