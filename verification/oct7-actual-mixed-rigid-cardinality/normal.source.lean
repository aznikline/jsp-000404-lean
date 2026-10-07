import Jsp000404.ActualHullSmallScoreTypes
import Jsp000404.ActualInteriorOneAngleGap
import Jsp000404.ActualRigidCardinality

set_option autoImplicit false

/-! Mixed original interior-light and nonacute-heavy selections.
The physical windows, full-hull membership and angle dichotomies are
produced internally. A heavy input only supplies an actual large angle
between two original rays; no class or rigidity certificate is an input.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualMixedRigidCardinality

/-- The physical coordinates of an actual hull window bound every
original pair of rays. This proof only uses the public Window fields. -/
theorem actual_window_angle_le_width {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p)
    (hleg : Section4Legality c lam) (i j : Fin s) (hi : i ≠ p) (hj : j ≠ p) :
    ∠ (c i) (c p) (c j) ≤ W.width := by
  have hui : c i - c p ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hi)
  have huj : c j - c p ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hj)
  have hang : ∠ (c i) (c p) (c j) = |W.theta j - W.theta i| := by
    change InnerProductGeometry.angle (c i - c p) (c j - c p) = _
    rw [o.angle_eq_abs_oangle_toReal hui huj,
      ← o.oangle_sub_left W.base_ne_zero hui huj,
      W.actual_direction i hi, W.actual_direction j hj, ← Real.Angle.coe_sub]
    rw [Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨by linarith [(W.theta_mem j hj).1, (W.theta_mem i hi).2, W.width_lt_pi],
        by linarith [(W.theta_mem j hj).2, (W.theta_mem i hi).1, W.width_lt_pi]⟩]
  rw [hang]
  apply abs_sub_le_iff.mpr
  constructor <;> linarith [(W.theta_mem i hi).1, (W.theta_mem i hi).2,
    (W.theta_mem j hj).1, (W.theta_mem j hj).2]

/-- An original score-two center with an actual angle at least twice
lambda cannot be HA. Its internally produced HM/HO clumps give the
angle dichotomy on all original rays. -/
theorem actual_heavy_large_angle_gap {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (hupper : lam ≤ Real.pi / 4)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (hlarge : ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b)) :
    ∀ i j : Fin s, i ≠ p → j ≠ p →
      ∠ (c i) (c p) (c j) ≤ Real.pi - 4 * lam ∨
        2 * lam ≤ ∠ (c i) (c p) (c j) := by
  have hrho : Real.pi / ((4 : ℝ) + 1 / 2) = 2 * Real.pi / 9 := by ring
  have hlo' : Real.pi / ((4 : ℝ) + 1 / 2) < lam := by rw [hrho]; exact hlo
  obtain ⟨hn, _, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by decide : 2 ≤ 4) hleg.lam_pos hlo' hupper
  have hcells := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos p
    (by omega : 2 ≤ s) hn
  have hscore := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hcells
  have hsmall : rowDefect 4 lam (directionRow o e c p) ≤ 2 := by omega
  have hhull := FullHullInteriorDefect.low_defect_is_full_hull_vertex
    o e he hleg hn p hsmall
  obtain ⟨⟨W,K⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_two_type
    hs o e he hleg hlo p hhull hp
  cases K with
  | HA _hout hcone =>
      obtain ⟨a,b,ha,hb,_hab,hbig⟩ := hlarge
      have hangle := actual_window_angle_le_width W hleg a b ha hb
      have hpi : Real.pi < 5 * lam := by linarith [Real.pi_pos]
      exact False.elim (by linarith)
  | HM _hout _hconeLo _hconeHi D =>
      intro i j hi hj
      by_cases hsame : D.code i = D.code j
      · exact Or.inl (D.same_angle_le hleg i j hi hj hsame)
      · exact Or.inr (D.different_angle_ge hleg i j hi hj hsame)
  | HO _hout _hcone D =>
      intro i j hi hj
      by_cases hsame : D.code i = D.code j
      · exact Or.inl (D.same_angle_le hleg i j hi hj hsame)
      · have hangle := D.different_angle_ge hleg i j hi hj hsame
        exact Or.inr (by linarith [hleg.lam_pos])

/-- Select original centers that are either original interior score-one
points or original score-two points with an actual large-angle witness.
There are at most four. Original full-hull facts are never transferred
to the selected subconfiguration; only proved physical angles restrict. -/
theorem actual_mixed_rigid_card_le_four {s r : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (hupper : lam ≤ Real.pi / 4)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick)
    (hselected : ∀ a : Fin r,
      (¬ IsHullVertex c (pick a) ∧ rowScore lam (directionRow o e c (pick a)) = 1) ∨
      (rowScore lam (directionRow o e c (pick a)) = 2 ∧
        ∃ u v : Fin s, u ≠ pick a ∧ v ≠ pick a ∧ u ≠ v ∧
          2 * lam ≤ ∠ (c u) (c (pick a)) (c v))) : r ≤ 4 := by
  by_cases hr : r ≤ 4
  · exact hr
  have hrs : r ≤ s := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective pick hpick
  have hs : 3 ≤ s := by omega
  have hgap : ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k →
      ∠ ((c ∘ pick) i) ((c ∘ pick) j) ((c ∘ pick) k) ≤ Real.pi - 4 * lam ∨
        2 * lam ≤ ∠ ((c ∘ pick) i) ((c ∘ pick) j) ((c ∘ pick) k) := by
    intro i j k hij hjk _hik
    have hij' : pick i ≠ pick j := hpick.ne hij
    have hkj' : pick k ≠ pick j := (hpick.ne hjk).symm
    rcases hselected j with ⟨hnot,hscore⟩ | ⟨hscore,hlarge⟩
    · exact ActualInteriorOneAngleGap.actual_interior_one_angle_gap
        (by omega : 2 ≤ s) o e he hleg hlo (pick j) hnot hscore hij' hkj'
    · exact actual_heavy_large_angle_gap hs o e he hleg hlo hupper
        (pick j) hscore hlarge (pick i) (pick k) hij' hkj'
  exact ActualRigidCardinality.card_le_four_of_actual_angle_gap
    (by omega : 2 ≤ r) o (hleg.restrict_injective pick hpick) hlo hupper hgap

#print axioms actual_window_angle_le_width
#print axioms actual_heavy_large_angle_gap
#print axioms actual_mixed_rigid_card_le_four

end Jsp404.ActualMixedRigidCardinality
