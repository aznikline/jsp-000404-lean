import Jsp000404.ActualF18TwoInterior
import Jsp000404.ActualF18SingleInterior
import Jsp000404.ActualHullTurnBudget

set_option autoImplicit false

/-!
Original all-light F18 assembly. Kernel validation of this module and its
new interior consumers is recorded separately; no pending source is READY.
All interior/hull cases are selected inside the original configuration.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualF18AllLight

private theorem all_hull_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (hall : ∀ i : Fin (s + 1), rowScore lam (directionRow o e c i) = 1)
    (hhull : ∀ i : Fin (s + 1), IsHullVertex c i) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hheavy : ActualF18Frame.heavyIndices o e c lam = ∅ := by
    ext i
    simp [ActualF18Frame.heavyIndices, hall i]
  have hN : s + 1 = 9 := by
    have h := F.card_plus_heavy
    rw [hheavy, Finset.card_empty, Nat.add_zero] at h
    exact h
  have hcard := ActualHullTurnBudget.selected_hull_card_le_eight
    o H.card_ge_three H.legality F.scale_lower
    (fun i : Fin (s + 1) => i) Function.injective_id hhull
  omega

/-- The all-light branch of the original F18 minimum counter-model is
impossible. The proof selects the original hull/interior cases internally;
the two-interior consumer has no premise about the remaining points. -/
theorem actual_F18_all_light_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (hall : ∀ i : Fin (s + 1), rowScore lam (directionRow o e c i) = 1) : False := by
  classical
  by_cases hhull : ∀ i : Fin (s + 1), IsHullVertex c i
  · exact all_hull_false o e he H hF hall hhull
  · push Not at hhull
    obtain ⟨p, hp⟩ := hhull
    by_cases hothers : ∀ q : Fin (s + 1), q ≠ p → IsHullVertex c q
    · exact ActualF18SingleInterior.actual_F18_all_light_single_interior_false
        o e he H hF hall p hp hothers
    · push Not at hothers
      obtain ⟨q, hqp, hq⟩ := hothers
      exact ActualF18TwoInterior.actual_F18_all_light_two_interior_false
        o e he H hF hall p q hqp.symm hp hq

/-- The original F18 model must contain an original score-two center.
The Frame dichotomy and the all-light contradiction are both internal. -/
theorem actual_F18_has_heavy {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18) :
    ∃ p : Fin (s + 1), rowScore lam (directionRow o e c p) = 2 := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  by_contra hnone
  have hall (i : Fin (s + 1)) : rowScore lam (directionRow o e c i) = 1 := by
    rcases F.score_one_or_two i with hlight | hheavy
    · exact hlight
    · exact False.elim (hnone ⟨i, hheavy⟩)
  exact actual_F18_all_light_false o e he H hF hall

#print axioms actual_F18_all_light_false
#print axioms actual_F18_has_heavy

end Jsp404.ActualF18AllLight
