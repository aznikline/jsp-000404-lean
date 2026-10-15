import Jsp000404.K3bArcAux2

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- `b` on the forward arc `a → c` splits it. -/
theorem cyclicDiff_eq_add_of_le {a b c : ℝ}
    (ha : a ∈ Set.Ico 0 Real.pi) (hb : b ∈ Set.Ico 0 Real.pi)
    (hc : c ∈ Set.Ico 0 Real.pi)
    (h : cyclicDiff a b ≤ cyclicDiff a c) :
    cyclicDiff a c = cyclicDiff a b + cyclicDiff b c := by
  obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hc0, hc1⟩ := hc
  rcases eq_or_ne a c with rfl | hac
  · have haa : cyclicDiff a a = (0 : ℝ) := by simp [cyclicDiff]
    rw [haa] at h
    have hab0 : cyclicDiff a b = 0 :=
      le_antisymm h (cyclicDiff_nonneg ha1 hb0)
    have hab : a = b :=
      cyclicDiff_eq_zero_of_Ico ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hab0
    subst hab; simp [cyclicDiff]
  rcases eq_or_ne a b with rfl | hab
  · simp [cyclicDiff]
  rcases eq_or_ne b c with rfl | hbc
  · have hbb : cyclicDiff b b = (0 : ℝ) := by simp [cyclicDiff]
    rw [hbb]; simp
  rcases lt_or_gt_of_ne hab with h12 | h21 <;>
    rcases lt_or_gt_of_ne hac with h13 | h31 <;>
    rcases lt_or_gt_of_ne hbc with h23 | h32 <;>
    unfold cyclicDiff at h ⊢ <;>
    split_ifs at h ⊢ <;> (try contradiction) <;>
    linarith [Real.pi_pos]


end Jsp404
