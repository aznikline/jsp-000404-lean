import Jsp000404.ActualPureLightBlock
import Jsp000404.ActualHullTurnBudget

set_option autoImplicit false

/-!
SOURCE_ONLY actual F18 one-heavy all-hull consumer.
The original point count, heavy hull membership and HA/HM/HO split are
derived internally. The public theorem accepts no wide angle, window,
type, integer weight, circle budget, or lower-cap certificate.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18OneHeavyAllHull

private theorem exceptional_weight_sum {s j : ℕ} (hj : 1 ≤ j) (p : Fin (s + 1)) :
    (∑ i : Fin (s + 1), if i = p then j else 1) = (s + 1) + (j - 1) := by
  classical
  have hsplit (i : Fin (s + 1)) :
      (if i = p then j else 1) = 1 + if i = p then j - 1 else 0 := by
    by_cases hip : i = p
    · simp only [ite_eq_left hip]
      omega
    · simp only [ite_eq_right hip, Nat.add_zero]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp

/-- All selected vertices are original full-hull vertices. Stronger
caps are supplied as actual angles, so the turn-budget producer may
choose its own physical windows without any window-coherence premise. -/
private theorem weighted_original_hull_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2))
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hs : 3 ≤ s + 1) (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (hN : s + 1 = 8)
    (hhull : ∀ q : Fin (s + 1), IsHullVertex c q)
    (p : Fin (s + 1)) (j : ℕ) (hj : 2 ≤ j)
    (hstrong : ∀ a b : Fin (s + 1), a ≠ p → b ≠ p → a ≠ b →
      ∠ (c a) (c p) (c b) ≤ Real.pi - (j : ℝ) * lam) : False := by
  classical
  let k : Fin (s + 1) → ℕ := fun i => if i = p then j else 1
  have hbudget := ActualHullTurnBudget.selected_hull_integer_budget_le_eight
    o hs (by omega : 2 ≤ s + 1) hleg hlo
    (fun i : Fin (s + 1) => i) (fun _ _ h => h) hhull k (by
      intro i a b hai hbi hab
      by_cases hip : i = p
      · subst i
        simpa [k] using hstrong a b hai hbi hab
      · simpa [k, hip] using hleg.triAngle a i b hai hbi.symm hab)
  have hcount := hbudget.2
  have hsum : (∑ i : Fin (s + 1), k i) = 8 + (j - 1) := by
    calc
      (∑ i : Fin (s + 1), k i) = (s + 1) + (j - 1) := by
        simpa only [k] using exceptional_weight_sum (by omega : 1 ≤ j) p
      _ = 8 + (j - 1) := by rw [hN]
  rw [hsum] at hcount
  omega

/-- The full original one-heavy all-hull F18 profile is impossible.
In particular, no actual wide-angle or HO classification is a premise. -/
theorem actual_F18_one_heavy_all_hull_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 2)
    (hother : ∀ q : Fin (s + 1), q ≠ p →
      rowScore lam (directionRow o e c q) = 1 ∧ IsHullVertex c q) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hheavy : ActualF18Frame.heavyIndices o e c lam = {p} := by
    ext q
    simp only [ActualF18Frame.heavyIndices, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      by_contra hqp
      have hqone := (hother q hqp).1
      omega
    · intro hqp
      simpa only [hqp] using hp
  have hN : s + 1 = 8 := by
    have hcard := F.card_plus_heavy
    rw [hheavy, Finset.card_singleton] at hcard
    omega
  have hhull (q : Fin (s + 1)) : IsHullVertex c q := by
    by_cases hqp : q = p
    · simpa only [hqp] using F.heavy_full_hull p hp
    · exact (hother q hqp).2
  obtain ⟨⟨W, kind⟩⟩ :=
    ActualHullSmallScoreTypes.exists_actual_hull_two_type
      H.card_ge_three o e he H.legality F.scale_lower p (hhull p) hp
  cases kind with
  | HA _hout hcone =>
      apply weighted_original_hull_false o H.card_ge_three H.legality F.scale_lower
        hN hhull p 3 (by decide)
      intro a b hap hbp _hab
      exact (ActualMixedRigidCardinality.actual_window_angle_le_width
        W H.legality a b hap hbp).trans hcone
  | HM _hout _hconeLo hconeHi _D =>
      apply weighted_original_hull_false o H.card_ge_three H.legality F.scale_lower
        hN hhull p 2 (by decide)
      intro a b hap hbp _hab
      exact (ActualMixedRigidCardinality.actual_window_angle_le_width
        W H.legality a b hap hbp).trans hconeHi
  | HO _hout hcone _D =>
      apply ActualPureLightBlock.actual_F18_one_heavy_all_hull_three_scale_angle_false
        o e he H hF p hp
      · intro q hqp
        exact ⟨(hother q hqp).2, (hother q hqp).1⟩
      · exact ⟨W.left, W.right, W.left_ne_center, W.right_ne_center,
          W.boundary_distinct, W.width_eq_actual_angle ▸ hcone⟩

#print axioms actual_F18_one_heavy_all_hull_false

end Jsp404.ActualF18OneHeavyAllHull
