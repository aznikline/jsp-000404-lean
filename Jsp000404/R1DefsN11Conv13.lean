import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Fin.Basic
import Jsp000404.R1DefsN11Base
set_option maxHeartbeats 1600000

namespace R2N4

open List

set_option maxHeartbeats 4000000 in
theorem msig1_11_L_R_of_pos_9 {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ x8 ∧ x8 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (x7 - x6) < 2 * lam ∧ (x8 - x7) < 2 * lam ∧ 2 * lam <= (tl + p - x8) ∧ (tl + p - x8) < 3 * lam)
    {c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℝ} (hp : List.Perm [x0, x1, x2, x3, x4, x5, x6, x7, x8] [c0, c1, c2, c3, c4, c5, c6, c7, c8]) :
    CMSig1_11_L_R lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases (mem9or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem9or (hp.subset (show x8 ∈ [x0, x1, x2, x3, x4, x5, x6, x7, x8] by simp))
    rcases hm with h | h | h | h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))))))
  · have hm := mem9or (hp.subset (show x0 ∈ [x0, x1, x2, x3, x4, x5, x6, x7, x8] by simp))
    rcases hm with h | h | h | h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))))))

end R2N4
