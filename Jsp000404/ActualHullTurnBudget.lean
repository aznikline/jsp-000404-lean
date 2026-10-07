import Jsp000404.ActualHullRayWindow
import Jsp000404.PositiveRowCount

set_option autoImplicit false

/-!
Circle budgets for an injective selection of full original hull vertices.

The windows and bisectors are produced from the original configuration.
The integer-weight theorem has an explicit actual-angle hypothesis for
future hull-type producers; it assumes no circle budget or cardinality bound.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualHullTurnBudget

/-- Actual full-hull windows, chosen internally for the selected original
vertices, satisfy their weighted circle budget. The selected rays are
restrictions of the original physical windows, not newly assumed cones. -/
theorem exists_selected_hull_turn_budget {s r : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 3 ≤ s) (hr : 2 ≤ r)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick)
    (hhull : ∀ i, IsHullVertex c (pick i)) :
    ∃ W : (i : Fin r) → ActualHullRayWindow.Window o c lam (pick i),
      ∑ i, (Real.pi - (W i).width) ≤ 2 * Real.pi := by
  classical
  let W : (i : Fin r) → ActualHullRayWindow.Window o c lam (pick i) :=
    fun i => Classical.choice
      (ActualHullRayWindow.exists_actual_hull_ray_window o hs hleg (pick i) (hhull i))
  refine ⟨W, ?_⟩
  apply PositiveRowCount.turn_budget_of_ray_windows o hr (c ∘ pick)
    (hleg.inj.comp hpick) (fun i => (W i).width)
    (fun i => (W i).width_pos.le) (fun i => (W i).width_lt_pi)
    (fun i => (W i).base) (fun i => (W i).base_ne_zero)
    (fun i j => (W i).theta (pick j.val))
  intro i j
  have hji : pick j.val ≠ pick i := hpick.ne j.property
  exact ⟨(W i).theta_mem (pick j.val) hji,
    (W i).actual_direction (pick j.val) hji⟩

/-- At `lam > 2*pi/9`, an injective selection of full original hull
vertices has at most eight entries. No caller-supplied ray chart is needed. -/
theorem selected_hull_card_le_eight {s r : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 3 ≤ s)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlam : 2 * Real.pi / 9 < lam)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick)
    (hhull : ∀ i, IsHullVertex c (pick i)) :
    r ≤ 8 := by
  classical
  by_cases hr : 2 ≤ r
  · obtain ⟨W, hbudget⟩ := exists_selected_hull_turn_budget o hs hr hleg pick hpick hhull
    have hweight (i : Fin r) : lam ≤ Real.pi - (W i).width := by
      linarith [(W i).width_le_legality]
    have hsum : (r : ℝ) * lam ≤ ∑ i : Fin r, (Real.pi - (W i).width) := by
      calc
        (r : ℝ) * lam = ∑ _i : Fin r, lam := by simp
        _ ≤ ∑ i : Fin r, (Real.pi - (W i).width) :=
          Finset.sum_le_sum (fun i _ => hweight i)
    by_contra hnot
    have hrnine : 9 ≤ r := by omega
    have hrreal : (9 : ℝ) ≤ r := by exact_mod_cast hrnine
    have hmul := mul_le_mul_of_nonneg_right hrreal hleg.lam_pos.le
    nlinarith
  · omega

/-- For at least two selected full-hull vertices, stronger actual angle
caps give the integer circle budget and its bound of eight. The hypothesis is on
all original angles at each selected vertex, including the internally
chosen actual boundary witnesses. It is not an assumed total capacity. -/
theorem selected_hull_integer_budget_le_eight {s r : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 3 ≤ s) (hr : 2 ≤ r)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlam : 2 * Real.pi / 9 < lam)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick)
    (hhull : ∀ i, IsHullVertex c (pick i)) (k : Fin r → ℕ)
    (hcap : ∀ (i : Fin r) (a b : Fin s),
      a ≠ pick i → b ≠ pick i → a ≠ b →
      ∠ (c a) (c (pick i)) (c b) ≤ Real.pi - (k i : ℝ) * lam) :
    ((∑ i, k i : ℕ) : ℝ) * lam ≤ 2 * Real.pi ∧ (∑ i, k i : ℕ) ≤ 8 := by
  classical
  obtain ⟨W, hbudget⟩ := exists_selected_hull_turn_budget o hs hr hleg pick hpick hhull
  have hweight (i : Fin r) : (k i : ℝ) * lam ≤ Real.pi - (W i).width := by
    have hactual := hcap i (W i).left (W i).right
      (W i).left_ne_center (W i).right_ne_center (W i).boundary_distinct
    rw [← (W i).width_eq_actual_angle] at hactual
    linarith
  have hsum : ((∑ i, k i : ℕ) : ℝ) * lam ≤
      ∑ i : Fin r, (Real.pi - (W i).width) := by
    calc
      ((∑ i, k i : ℕ) : ℝ) * lam = ∑ i : Fin r, (k i : ℝ) * lam := by
        simp only [Nat.cast_sum, Finset.sum_mul]
      _ ≤ ∑ i : Fin r, (Real.pi - (W i).width) :=
        Finset.sum_le_sum (fun i _ => hweight i)
  have hcircle : ((∑ i, k i : ℕ) : ℝ) * lam ≤ 2 * Real.pi := hsum.trans hbudget
  refine ⟨hcircle, ?_⟩
  by_contra hnot
  have hknine : 9 ≤ ∑ i, k i := by omega
  have hkreal : (9 : ℝ) ≤ ((∑ i, k i : ℕ) : ℝ) := by exact_mod_cast hknine
  have hmul := mul_le_mul_of_nonneg_right hkreal hleg.lam_pos.le
  nlinarith

#print axioms exists_selected_hull_turn_budget
#print axioms selected_hull_card_le_eight
#print axioms selected_hull_integer_budget_le_eight

end Jsp404.ActualHullTurnBudget
