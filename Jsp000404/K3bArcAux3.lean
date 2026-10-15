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
  rcases lt_or_gt_of_ne hab with h12 | h21
  · rcases lt_or_gt_of_ne hac with h13 | h31
    · have hh : b - a ≤ c - a := by
        simpa [cyclicDiff, hab, hac, h12, h13] using h
      have h23 : b < c := by
        rcases lt_or_gt_of_ne hbc with ht | ht
        · exact ht
        · linarith
      simp only [cyclicDiff, if_neg hab, if_neg hac, if_neg hbc,
        if_pos h12, if_pos h13, if_pos h23]
      ring
    · have h32 : c < b := lt_trans h31 h12
      simp only [cyclicDiff, if_neg hab, if_neg hac, if_neg hbc,
        if_pos h12, if_neg (not_lt.mpr h31.le),
        if_neg (not_lt.mpr h32.le)]
      ring
  · rcases lt_or_gt_of_ne hac with h13 | h31
    · have hh : Real.pi + b - a ≤ c - a := by
        simpa [cyclicDiff, hab, hac, not_lt.mpr h21.le, h13] using h
      linarith
    · have hh : Real.pi + b - a ≤ Real.pi + c - a := by
        simpa [cyclicDiff, hab, hac, not_lt.mpr h21.le,
          not_lt.mpr h31.le] using h
      have h23 : b < c := by
        rcases lt_or_gt_of_ne hbc with ht | ht
        · exact ht
        · linarith
      simp only [cyclicDiff, if_neg hab, if_neg hac, if_neg hbc,
        if_neg (not_lt.mpr h21.le), if_neg (not_lt.mpr h31.le),
        if_pos h23]
      ring


end Jsp404
