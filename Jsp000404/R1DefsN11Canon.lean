import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Fin.Basic
import Jsp000404.R1DefsN11Conv01
import Jsp000404.R1DefsN11Conv02
import Jsp000404.R1DefsN11Conv03
import Jsp000404.R1DefsN11Conv04
import Jsp000404.R1DefsN11Conv05
import Jsp000404.R1DefsN11Conv06
import Jsp000404.R1DefsN11Conv07
import Jsp000404.R1DefsN11Conv08
import Jsp000404.R1DefsN11Conv09
import Jsp000404.R1DefsN11Conv10
import Jsp000404.R1DefsN11Conv11
import Jsp000404.R1DefsN11Conv12
import Jsp000404.R1DefsN11Conv13
set_option maxHeartbeats 1600000

namespace R2N4

open List

theorem msig2_11_canon_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ x8 ∧ x8 ≤ tl + p)
    (hs : RowSig2_11 lam p tl x0 x1 x2 x3 x4 x5 x6 x7 x8)
    {c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℝ}
    (hp : List.Perm [x0, x1, x2, x3, x4, x5, x6, x7, x8] [c0, c1, c2, c3, c4, c5, c6, c7, c8])
    (hsp : ∀ z ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8], lam ≤ z ∧ z < 5 * lam) :
    CMSig2_11_H_L lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 ∨
    CMSig2_11_H_I lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 ∨
    CMSig2_11_H_R lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 ∨
    CMSig2_11_M_LI lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 ∨
    CMSig2_11_M_LR lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 ∨
    CMSig2_11_M_IR lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 := by
  rcases hs with s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s | s
  · exact (Or.inl (msig2_11_H_L_of_pos_0 hl hord s hp))
  · exact (Or.inr (Or.inl (msig2_11_H_I_of_pos_1 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig2_11_H_I_of_pos_2 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig2_11_H_I_of_pos_3 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig2_11_H_I_of_pos_4 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig2_11_H_I_of_pos_5 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig2_11_H_I_of_pos_6 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig2_11_H_I_of_pos_7 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig2_11_H_I_of_pos_8 hl hord s hp)))
  · exact (Or.inr (Or.inr (Or.inl (msig2_11_H_R_of_pos_9 hl hord s hp))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (msig2_11_M_LI_of_pos_10 hl hord s hp)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (msig2_11_M_LI_of_pos_11 hl hord s hp)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (msig2_11_M_LI_of_pos_12 hl hord s hp)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (msig2_11_M_LI_of_pos_13 hl hord s hp)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (msig2_11_M_LI_of_pos_14 hl hord s hp)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (msig2_11_M_LI_of_pos_15 hl hord s hp)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (msig2_11_M_LI_of_pos_16 hl hord s hp)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (msig2_11_M_LI_of_pos_17 hl hord s hp)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (msig2_11_M_LR_of_pos_18 hl hord s hp))))))
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x0 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x2 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x0 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x3 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x0 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x4 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x0 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x5 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x0 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x6 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x0 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x7 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x0 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x8 (hp.subset (by simp))
    linarith
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (msig2_11_M_IR_of_pos_26 hl hord s hp))))))
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x1 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x3 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x1 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x4 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x1 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x5 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x1 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x6 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x1 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x7 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x1 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x8 (hp.subset (by simp))
    linarith
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (msig2_11_M_IR_of_pos_33 hl hord s hp))))))
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x2 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x4 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x2 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x5 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x2 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x6 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x2 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x7 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x2 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x8 (hp.subset (by simp))
    linarith
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (msig2_11_M_IR_of_pos_39 hl hord s hp))))))
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x3 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x5 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x3 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x6 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x3 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x7 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x3 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x8 (hp.subset (by simp))
    linarith
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (msig2_11_M_IR_of_pos_44 hl hord s hp))))))
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x4 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x6 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x4 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x7 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x4 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x8 (hp.subset (by simp))
    linarith
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (msig2_11_M_IR_of_pos_48 hl hord s hp))))))
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x5 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x7 (hp.subset (by simp))
    linarith
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x5 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x8 (hp.subset (by simp))
    linarith
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (msig2_11_M_IR_of_pos_51 hl hord s hp))))))
  · exfalso
    obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := s
    obtain ⟨hAl, hAu⟩ := hsp x6 (hp.subset (by simp))
    obtain ⟨hBl, hBu⟩ := hsp x8 (hp.subset (by simp))
    linarith
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (msig2_11_M_IR_of_pos_53 hl hord s hp))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (msig2_11_M_IR_of_pos_54 hl hord s hp))))))

theorem msig1_11_canon_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ x8 ∧ x8 ≤ tl + p)
    (hs : RowSig1_11 lam p tl x0 x1 x2 x3 x4 x5 x6 x7 x8)
    {c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℝ}
    (hp : List.Perm [x0, x1, x2, x3, x4, x5, x6, x7, x8] [c0, c1, c2, c3, c4, c5, c6, c7, c8]) :
    CMSig1_11_L_0 lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 ∨
    CMSig1_11_L_I lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 ∨
    CMSig1_11_L_R lam p tl c0 c1 c2 c3 c4 c5 c6 c7 c8 := by
  rcases hs with s | s | s | s | s | s | s | s | s | s
  · exact (Or.inl (msig1_11_L_0_of_pos_0 hl hord s hp))
  · exact (Or.inr (Or.inl (msig1_11_L_I_of_pos_1 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig1_11_L_I_of_pos_2 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig1_11_L_I_of_pos_3 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig1_11_L_I_of_pos_4 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig1_11_L_I_of_pos_5 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig1_11_L_I_of_pos_6 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig1_11_L_I_of_pos_7 hl hord s hp)))
  · exact (Or.inr (Or.inl (msig1_11_L_I_of_pos_8 hl hord s hp)))
  · exact (Or.inr (Or.inr (msig1_11_L_R_of_pos_9 hl hord s hp)))

end R2N4
