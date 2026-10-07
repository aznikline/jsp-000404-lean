import Jsp000404.ActualF18Frame
import Jsp000404.ActualInteriorOneRuns
import Jsp000404.ActualHeavyNearestExclusion
import Jsp000404.ActualNoThreeNonacuteHeavy
import Jsp000404.ActualHullTurnBudget

set_option autoImplicit false

/-!
Actual F18 three-heavy consumers. All nearest neighbors and hull windows
are constructed from the original points. No nearest-neighbor map, type
array, or circle budget is a caller premise. Validation is recorded separately.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18ThreeHeavyAcute

private theorem wide_of_window_lower {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (W : ActualHullRayWindow.Window o c lam p) (hlower : 2 * lam ≤ W.width) :
    ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b) := by
  exact ⟨W.left, W.right, W.left_ne_center, W.right_ne_center,
    W.boundary_distinct, W.width_eq_actual_angle ▸ hlower⟩

private theorem heavy_nearest_has_acute_window {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (F : ActualF18Frame.Frame o e c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (q : Fin s) (hpq : p ≠ q)
    (hnear : ∀ j : Fin s, q ≠ j → dist (c q) (c p) ≤ dist (c q) (c j)) :
    ∃ W : ActualHullRayWindow.Window o c lam p, W.width ≤ Real.pi - 3 * lam := by
  obtain ⟨⟨W, K⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_two_type
    H.card_ge_three o e he H.legality F.scale_lower p (F.heavy_full_hull p hp) hp
  cases K with
  | HA _hout hcone => exact ⟨W, hcone⟩
  | HM _hout hlo _hhi _D =>
      have hwide := wide_of_window_lower W hlo
      exact False.elim
        (ActualHeavyNearestExclusion.actual_nonacute_heavy_not_weak_nearest
          o e he H p hp hwide q hpq hnear)
  | HO _hout hlo _D =>
      have hwide := wide_of_window_lower W (by linarith [H.legality.lam_pos])
      exact False.elim
        (ActualHeavyNearestExclusion.actual_nonacute_heavy_not_weak_nearest
          o e he H p hp hwide q hpq hnear)

/-- The original three-heavy F18 branch with no original hull light is
impossible. The three light targets internally choose actual weak nearest
neighbors, which must be distinct acute heavy hull centers. Their actual
windows spend nine lambda units in the checked circle budget of eight. -/
theorem actual_F18_three_heavy_no_hull_light_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (ht : (ActualF18Frame.heavyIndices o e c lam).card = 3)
    (hnoHullLight : ∀ q : Fin (s + 1),
      rowScore lam (directionRow o e c q) = 1 → ¬ IsHullVertex c q) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hs : 3 ≤ s := by have := F.card_ge_six; omega
  let L := ActualF18Frame.lightIndices o e c lam
  have hL : L.card = 3 := by
    have h := F.light_plus_twice_heavy
    change L.card + 2 * (ActualF18Frame.heavyIndices o e c lam).card = 9 at h
    omega
  let E := L.orderIsoOfFin hL
  let target : Fin 3 → Fin (s + 1) := fun j => (E j).val
  have htarget : Function.Injective target := Subtype.val_injective.comp E.injective
  have htargetScore (j : Fin 3) : rowScore lam (directionRow o e c (target j)) = 1 :=
    (Finset.mem_filter.mp (E j).property).2
  have hnearest (j : Fin 3) : ∃ p : Fin (s + 1), p ≠ target j ∧ IsHullVertex c p ∧
      ∀ k : Fin (s + 1), target j ≠ k → dist (c (target j)) (c p) ≤ dist (c (target j)) (c k) :=
    ActualInteriorOneRuns.exists_actual_low_four_F18_light_nearest_full_hull
      hs o e he H hF (target j) (htargetScore j)
  choose receiver hreceiverNe hreceiverHull hreceiverNear using hnearest
  have hreceiverScore (j : Fin 3) : rowScore lam (directionRow o e c (receiver j)) = 2 := by
    rcases F.score_one_or_two (receiver j) with hlight | hheavy
    · exact False.elim (hnoHullLight (receiver j) hlight (hreceiverHull j))
    · exact hheavy
  have hwindows (j : Fin 3) : ∃ W : ActualHullRayWindow.Window o c lam (receiver j),
      W.width ≤ Real.pi - 3 * lam :=
    heavy_nearest_has_acute_window o e he H F (receiver j) (hreceiverScore j)
      (target j) (hreceiverNe j) (hreceiverNear j)
  choose W hwidth using hwindows
  have hsmall : Real.pi - 3 * lam < Real.pi / 3 := by linarith [F.scale_lower]
  have hreceiver : Function.Injective receiver := by
    intro i j hij
    have hne : receiver i ≠ target j := by
      rw [hij]
      exact hreceiverNe j
    have hnearj : ∀ k : Fin (s + 1), target j ≠ k →
        dist (c (target j)) (c (receiver i)) ≤ dist (c (target j)) (c k) := by
      simpa only [hij] using hreceiverNear j
    have hangle := ActualMixedRigidCardinality.actual_window_angle_le_width (W i)
      H.legality (target i) (target j) (hreceiverNe i).symm hne.symm
    have heq := SharpNearestGeometry.actual_nearest_indices_eq_of_small_anchor_angle
      H.legality (hreceiverNe i) hne (hreceiverNear i) hnearj
      (hangle.trans_lt ((hwidth i).trans_lt hsmall))
    exact htarget heq
  have hbudget := ActualHullTurnBudget.selected_hull_integer_budget_le_eight
    o H.card_ge_three (by decide : 2 ≤ 3) H.legality F.scale_lower
    receiver hreceiver hreceiverHull (fun _ : Fin 3 => 3) (by
      intro i a b ha hb _hab
      exact (ActualMixedRigidCardinality.actual_window_angle_le_width (W i)
        H.legality a b ha hb).trans (hwidth i))
  have hcount := hbudget.2
  norm_num at hcount

/-- In the whole original three-heavy F18 branch, at least one heavy has
an actual acute HA window. This consumes the checked NoThree theorem before
the remaining cases with one or more original hull lights are considered. -/
theorem actual_F18_three_heavy_exists_acute_window {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (ht : (ActualF18Frame.heavyIndices o e c lam).card = 3) :
    ∃ p : Fin s, rowScore lam (directionRow o e c p) = 2 ∧
      ∃ W : ActualHullRayWindow.Window o c lam p,
        gapScore lam (Real.pi - W.width) = 2 ∧ W.width ≤ Real.pi - 3 * lam := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  let P := ActualF18Frame.heavyIndices o e c lam
  have hP : P.card = 3 := ht
  let E := P.orderIsoOfFin hP
  let pick : Fin 3 → Fin s := fun i => (E i).val
  have hpick : Function.Injective pick := Subtype.val_injective.comp E.injective
  have hscore (i : Fin 3) : rowScore lam (directionRow o e c (pick i)) = 2 :=
    (Finset.mem_filter.mp (E i).property).2
  by_contra hnone
  have hwide (i : Fin 3) : ∃ a b : Fin s, a ≠ pick i ∧ b ≠ pick i ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c (pick i)) (c b) := by
    obtain ⟨⟨W, K⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_two_type
      H.card_ge_three o e he H.legality F.scale_lower
      (pick i) (F.heavy_full_hull (pick i) (hscore i)) (hscore i)
    cases K with
    | HA hout hcone => exact False.elim (hnone ⟨pick i, hscore i, W, hout, hcone⟩)
    | HM _hout hlo _hhi _D => exact wide_of_window_lower W hlo
    | HO _hout hlo _D => exact wide_of_window_lower W (by linarith [H.legality.lam_pos])
  exact ActualNoThreeNonacuteHeavy.no_three_nonacute_heavy o e he H pick hpick hscore hwide

#print axioms actual_F18_three_heavy_no_hull_light_false
#print axioms actual_F18_three_heavy_exists_acute_window

end Jsp404.ActualF18ThreeHeavyAcute
