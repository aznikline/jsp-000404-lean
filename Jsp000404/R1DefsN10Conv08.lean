import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Fin.Basic
import Jsp000404.R1DefsN10Base
set_option maxHeartbeats 1600000

namespace R2N4

open List

set_option maxHeartbeats 4000000 in
theorem msig2_10_M_IR_of_pos_41 {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 x4 x5 x6 x7 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (x6 - x5) < 2 * lam ∧ (x7 - x6) < 2 * lam ∧ 2 * lam <= (tl + p - x7) ∧ (tl + p - x7) < 3 * lam)
    {c0 c1 c2 c3 c4 c5 c6 c7 : ℝ} (hp : List.Perm [x0, x1, x2, x3, x4, x5, x6, x7] [c0, c1, c2, c3, c4, c5, c6, c7]) :
    CMSig2_10_M_IR lam p tl c0 c1 c2 c3 c4 c5 c6 c7 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm := mem8or (hp.subset (show x0 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    rcases hm with h | h | h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))))
  · intro z hz
    rcases (mem8or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem8or (hp.subset (show x7 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    rcases hm with h | h | h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))))
  · have hm1 := mem8or (hp.subset (show x4 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    have hm2 := mem8or (hp.subset (show x5 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    rcases hm1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exfalso; linarith

set_option maxHeartbeats 4000000 in
theorem msig2_10_M_IR_of_pos_43 {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 x4 x5 x6 x7 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (x6 - x5) ∧ (x6 - x5) < 3 * lam ∧ (x7 - x6) < 2 * lam ∧ 2 * lam <= (tl + p - x7) ∧ (tl + p - x7) < 3 * lam)
    {c0 c1 c2 c3 c4 c5 c6 c7 : ℝ} (hp : List.Perm [x0, x1, x2, x3, x4, x5, x6, x7] [c0, c1, c2, c3, c4, c5, c6, c7]) :
    CMSig2_10_M_IR lam p tl c0 c1 c2 c3 c4 c5 c6 c7 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm := mem8or (hp.subset (show x0 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    rcases hm with h | h | h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))))
  · intro z hz
    rcases (mem8or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem8or (hp.subset (show x7 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    rcases hm with h | h | h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))))
  · have hm1 := mem8or (hp.subset (show x5 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    have hm2 := mem8or (hp.subset (show x6 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    rcases hm1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exfalso; linarith

set_option maxHeartbeats 4000000 in
theorem msig2_10_M_IR_of_pos_44 {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 x4 x5 x6 x7 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ 2 * lam <= (x7 - x6) ∧ (x7 - x6) < 3 * lam ∧ 2 * lam <= (tl + p - x7) ∧ (tl + p - x7) < 3 * lam)
    {c0 c1 c2 c3 c4 c5 c6 c7 : ℝ} (hp : List.Perm [x0, x1, x2, x3, x4, x5, x6, x7] [c0, c1, c2, c3, c4, c5, c6, c7]) :
    CMSig2_10_M_IR lam p tl c0 c1 c2 c3 c4 c5 c6 c7 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm := mem8or (hp.subset (show x0 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    rcases hm with h | h | h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))))
  · intro z hz
    rcases (mem8or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem8or (hp.subset (show x7 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    rcases hm with h | h | h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))))
  · have hm1 := mem8or (hp.subset (show x6 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    have hm2 := mem8or (hp.subset (show x7 ∈ [x0, x1, x2, x3, x4, x5, x6, x7] by simp))
    rcases hm1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c0 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c1 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c2 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c3 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c4 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c5 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c6 ∨ c7 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7], z ≤ c7 ∨ c6 ≤ z := by
          intro z hz
          rcases (mem8or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exfalso; linarith

end R2N4
