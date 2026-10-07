import Jsp000404.SecondStrip

/-!
A genuine scale-doubling consequence of an actual angular gap.
The gap is an explicit geometric condition, not a capacity premise.
The independent second-strip theorem then bounds the actual point count.
-/

set_option autoImplicit false
set_option pp.fullNames true

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualRigidCardinality

/-- A very small/large angle dichotomy promotes actual legality to twice
its old scale. Every triangle angle is derived, not supplied at the new scale. -/
theorem legality_at_double_scale {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (hgap : ∀ i j k : Fin s, i ≠ j → j ≠ k → i ≠ k →
      ∠ (c i) (c j) (c k) ≤ Real.pi - 4 * lam ∨
        2 * lam ≤ ∠ (c i) (c j) (c k)) :
    Section4Legality c (2 * lam) := by
  refine ⟨by linarith [hleg.lam_pos], hleg.inj, ?_⟩
  intro i j k hij hjk hik
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c i) (p₂ := c j) (c k) (hleg.inj.ne hij.symm)
  rw [EuclideanGeometry.angle_comm (c j) (c k) (c i),
    EuclideanGeometry.angle_comm (c k) (c i) (c j)] at hsum
  have hi := hgap j i k hij.symm hik hjk
  have hk := hgap i k j hik hjk.symm hij
  have hcap := hleg.triAngle i j k hij hjk hik
  have hi0 := EuclideanGeometry.angle_nonneg (c j) (c i) (c k)
  have hk0 := EuclideanGeometry.angle_nonneg (c i) (c k) (c j)
  by_contra hnot
  have hlarge : Real.pi - 2 * lam < ∠ (c i) (c j) (c k) := lt_of_not_ge hnot
  have hismall : ∠ (c j) (c i) (c k) ≤ Real.pi - 4 * lam := by
    rcases hi with hi | hi
    · exact hi
    · linarith
  have hksmall : ∠ (c i) (c k) (c j) ≤ Real.pi - 4 * lam := by
    rcases hk with hk | hk
    · exact hk
    · linarith
  linarith

/-- The real gap condition bounds ordinary cardinality by four. No inverse
realization or unproved sharp capacity at the old scale is used. -/
theorem card_le_four_of_actual_angle_gap {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (hupper : lam ≤ Real.pi / 4)
    (hgap : ∀ i j k : Fin s, i ≠ j → j ≠ k → i ≠ k →
      ∠ (c i) (c j) (c k) ≤ Real.pi - 4 * lam ∨
        2 * lam ≤ ∠ (c i) (c j) (c k)) : s ≤ 4 := by
  have hdouble := legality_at_double_scale hleg hlo hgap
  have hp : 0 < 2 * lam := hdouble.lam_pos
  have hratio0 : 0 ≤ Real.pi / (2 * lam) := div_nonneg Real.pi_pos.le hp.le
  have hratioLo : (2 : ℝ) ≤ Real.pi / (2 * lam) :=
    (le_div_iff₀ hp).mpr (by linarith)
  have hratioHi : Real.pi / (2 * lam) < (9 / 4 : ℝ) :=
    (div_lt_iff₀ hp).mpr (by linarith)
  have hn : Nat.floor (Real.pi / (2 * lam)) = 2 := by
    apply (Nat.floor_eq_iff hratio0).mpr
    constructor
    · simpa using hratioLo
    · norm_num
      linarith
  exact card_le_four_of_second_strip_low o hs hp hn (by linarith) hdouble

#print axioms legality_at_double_scale
#print axioms card_le_four_of_actual_angle_gap

end Jsp404.ActualRigidCardinality
