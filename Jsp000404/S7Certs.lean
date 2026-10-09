import Jsp000404.S7LeavessAA2_0
import Jsp000404.S7LeavessAA2_1
import Jsp000404.S7LeavessAA2_2
import Jsp000404.S7LeavessAA2_3
import Jsp000404.S7LeavessAA5_0
import Jsp000404.S7LeavessAA5_1
import Jsp000404.S7LeavessAA5_2
import Jsp000404.S7LeavessAA5_3
import Jsp000404.S7LeavessAA5_4
import Jsp000404.S7LeavessAB0_0
import Jsp000404.S7LeavessAB0_1
import Jsp000404.S7LeavessAB0_2
import Jsp000404.S7LeavessAB0_3
import Jsp000404.S7LeavessAB0_4
import Jsp000404.S7LeavessAB0_5
import Jsp000404.S7LeavessAB0_6
import Jsp000404.S7LeavessAB3_0
import Jsp000404.S7LeavessAB3_1
import Jsp000404.S7LeavessAB3_2
import Jsp000404.S7LeavessAB3_3
import Jsp000404.S7LeavessAB3_4
import Jsp000404.S7LeavessAB3_5
import Jsp000404.S7LeavessAB3_6

namespace R2N4


theorem s7cert_AA2 (m : N7Model)
    {x00 x01 x02 x03 x04 : ℝ}
    (ho0 : m.t 0 ≤ x00 ∧ x00 ≤ x01 ∧ x01 ≤ x02 ∧ x02 ≤ x03 ∧ x03 ≤ x04 ∧ x04 ≤ m.t 0 + m.p)
    (hs0 : RowSig2_7 m.lam m.p (m.t 0) x00 x01 x02 x03 x04)
    (hp0 : List.Perm [x00, x01, x02, x03, x04] [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)])
    {x10 x11 x12 x13 x14 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ x14 ∧ x14 ≤ m.t 1 + m.p)
    (hs1 : RowSig2_7 m.lam m.p (m.t 1) x10 x11 x12 x13 x14)
    (hp1 : List.Perm [x10, x11, x12, x13, x14] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)])
    {x20 x21 x22 x23 x24 : ℝ}
    (ho2 : m.t 2 ≤ x20 ∧ x20 ≤ x21 ∧ x21 ≤ x22 ∧ x22 ≤ x23 ∧ x23 ≤ x24 ∧ x24 ≤ m.t 2 + m.p)
    (hs2 : RowSig1_7 m.lam m.p (m.t 2) x20 x21 x22 x23 x24)
    (hp2 : List.Perm [x20, x21, x22, x23, x24] [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)])
    : False := by
  have hsp0 : ∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp1 : ∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp2 : ∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig2_7_canon_of_pos m.hlam ho0 hs0 hp0 hsp0 with c0 | c0 | c0 | c0 | c0 | c0
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_L_H_L_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_L_H_L_L_I m c0 c1 c2
      · exact n7l_sAA2_H_L_H_L_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_L_H_I_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_L_H_I_L_I m c0 c1 c2
      · exact n7l_sAA2_H_L_H_I_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_L_H_R_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_L_H_R_L_I m c0 c1 c2
      · exact n7l_sAA2_H_L_H_R_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_L_M_LI_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_L_M_LI_L_I m c0 c1 c2
      · exact n7l_sAA2_H_L_M_LI_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_L_M_LR_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_L_M_LR_L_I m c0 c1 c2
      · exact n7l_sAA2_H_L_M_LR_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_L_M_IR_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_L_M_IR_L_I m c0 c1 c2
      · exact n7l_sAA2_H_L_M_IR_L_R m c0 c1 c2
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_I_H_L_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_I_H_L_L_I m c0 c1 c2
      · exact n7l_sAA2_H_I_H_L_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_I_H_I_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_I_H_I_L_I m c0 c1 c2
      · exact n7l_sAA2_H_I_H_I_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_I_H_R_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_I_H_R_L_I m c0 c1 c2
      · exact n7l_sAA2_H_I_H_R_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_I_M_LI_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_I_M_LI_L_I m c0 c1 c2
      · exact n7l_sAA2_H_I_M_LI_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_I_M_LR_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_I_M_LR_L_I m c0 c1 c2
      · exact n7l_sAA2_H_I_M_LR_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_I_M_IR_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_I_M_IR_L_I m c0 c1 c2
      · exact n7l_sAA2_H_I_M_IR_L_R m c0 c1 c2
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_R_H_L_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_R_H_L_L_I m c0 c1 c2
      · exact n7l_sAA2_H_R_H_L_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_R_H_I_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_R_H_I_L_I m c0 c1 c2
      · exact n7l_sAA2_H_R_H_I_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_R_H_R_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_R_H_R_L_I m c0 c1 c2
      · exact n7l_sAA2_H_R_H_R_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_R_M_LI_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_R_M_LI_L_I m c0 c1 c2
      · exact n7l_sAA2_H_R_M_LI_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_R_M_LR_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_R_M_LR_L_I m c0 c1 c2
      · exact n7l_sAA2_H_R_M_LR_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_H_R_M_IR_L_0 m c0 c1 c2
      · exact n7l_sAA2_H_R_M_IR_L_I m c0 c1 c2
      · exact n7l_sAA2_H_R_M_IR_L_R m c0 c1 c2
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LI_H_L_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LI_H_L_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LI_H_L_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LI_H_I_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LI_H_I_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LI_H_I_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LI_H_R_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LI_H_R_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LI_H_R_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LI_M_LI_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LI_M_LI_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LI_M_LI_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LI_M_LR_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LI_M_LR_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LI_M_LR_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LI_M_IR_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LI_M_IR_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LI_M_IR_L_R m c0 c1 c2
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LR_H_L_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LR_H_L_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LR_H_L_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LR_H_I_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LR_H_I_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LR_H_I_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LR_H_R_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LR_H_R_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LR_H_R_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LR_M_LI_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LR_M_LI_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LR_M_LI_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LR_M_LR_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LR_M_LR_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LR_M_LR_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_LR_M_IR_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_LR_M_IR_L_I m c0 c1 c2
      · exact n7l_sAA2_M_LR_M_IR_L_R m c0 c1 c2
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_IR_H_L_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_IR_H_L_L_I m c0 c1 c2
      · exact n7l_sAA2_M_IR_H_L_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_IR_H_I_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_IR_H_I_L_I m c0 c1 c2
      · exact n7l_sAA2_M_IR_H_I_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_IR_H_R_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_IR_H_R_L_I m c0 c1 c2
      · exact n7l_sAA2_M_IR_H_R_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_IR_M_LI_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_IR_M_LI_L_I m c0 c1 c2
      · exact n7l_sAA2_M_IR_M_LI_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_IR_M_LR_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_IR_M_LR_L_I m c0 c1 c2
      · exact n7l_sAA2_M_IR_M_LR_L_R m c0 c1 c2
    · rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
      · exact n7l_sAA2_M_IR_M_IR_L_0 m c0 c1 c2
      · exact n7l_sAA2_M_IR_M_IR_L_I m c0 c1 c2
      · exact n7l_sAA2_M_IR_M_IR_L_R m c0 c1 c2

theorem s7cert_AA5 (m : N7Model)
    {x00 x01 x02 x03 x04 : ℝ}
    (ho0 : m.t 0 ≤ x00 ∧ x00 ≤ x01 ∧ x01 ≤ x02 ∧ x02 ≤ x03 ∧ x03 ≤ x04 ∧ x04 ≤ m.t 0 + m.p)
    (hs0 : RowSig2_7 m.lam m.p (m.t 0) x00 x01 x02 x03 x04)
    (hp0 : List.Perm [x00, x01, x02, x03, x04] [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)])
    {x10 x11 x12 x13 x14 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ x14 ∧ x14 ≤ m.t 1 + m.p)
    (hs1 : RowSig2_7 m.lam m.p (m.t 1) x10 x11 x12 x13 x14)
    (hp1 : List.Perm [x10, x11, x12, x13, x14] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)])
    {x50 x51 x52 x53 x54 : ℝ}
    (ho5 : m.t 5 ≤ x50 ∧ x50 ≤ x51 ∧ x51 ≤ x52 ∧ x52 ≤ x53 ∧ x53 ≤ x54 ∧ x54 ≤ m.t 5 + m.p)
    (hs5 : RowSig1_7 m.lam m.p (m.t 5) x50 x51 x52 x53 x54)
    (hp5 : List.Perm [x50, x51, x52, x53, x54] [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)])
    : False := by
  have hsp0 : ∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp1 : ∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp5 : ∀ z ∈ [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig2_7_canon_of_pos m.hlam ho0 hs0 hp0 hsp0 with c0 | c0 | c0 | c0 | c0 | c0
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_L_H_L_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_L_H_L_L_I m c0 c1 c5
      · exact n7l_sAA5_H_L_H_L_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_L_H_I_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_L_H_I_L_I m c0 c1 c5
      · exact n7l_sAA5_H_L_H_I_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_L_H_R_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_L_H_R_L_I m c0 c1 c5
      · exact n7l_sAA5_H_L_H_R_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_L_M_LI_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_L_M_LI_L_I m c0 c1 c5
      · exact n7l_sAA5_H_L_M_LI_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_L_M_LR_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_L_M_LR_L_I m c0 c1 c5
      · exact n7l_sAA5_H_L_M_LR_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_L_M_IR_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_L_M_IR_L_I m c0 c1 c5
      · exact n7l_sAA5_H_L_M_IR_L_R m c0 c1 c5
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_I_H_L_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_I_H_L_L_I m c0 c1 c5
      · exact n7l_sAA5_H_I_H_L_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_I_H_I_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_I_H_I_L_I m c0 c1 c5
      · exact n7l_sAA5_H_I_H_I_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_I_H_R_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_I_H_R_L_I m c0 c1 c5
      · exact n7l_sAA5_H_I_H_R_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_I_M_LI_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_I_M_LI_L_I m c0 c1 c5
      · exact n7l_sAA5_H_I_M_LI_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_I_M_LR_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_I_M_LR_L_I m c0 c1 c5
      · exact n7l_sAA5_H_I_M_LR_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_I_M_IR_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_I_M_IR_L_I m c0 c1 c5
      · exact n7l_sAA5_H_I_M_IR_L_R m c0 c1 c5
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_R_H_L_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_R_H_L_L_I m c0 c1 c5
      · exact n7l_sAA5_H_R_H_L_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_R_H_I_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_R_H_I_L_I m c0 c1 c5
      · exact n7l_sAA5_H_R_H_I_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_R_H_R_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_R_H_R_L_I m c0 c1 c5
      · exact n7l_sAA5_H_R_H_R_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_R_M_LI_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_R_M_LI_L_I m c0 c1 c5
      · exact n7l_sAA5_H_R_M_LI_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_R_M_LR_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_R_M_LR_L_I m c0 c1 c5
      · exact n7l_sAA5_H_R_M_LR_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_H_R_M_IR_L_0 m c0 c1 c5
      · exact n7l_sAA5_H_R_M_IR_L_I m c0 c1 c5
      · exact n7l_sAA5_H_R_M_IR_L_R m c0 c1 c5
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LI_H_L_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LI_H_L_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LI_H_L_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LI_H_I_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LI_H_I_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LI_H_I_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LI_H_R_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LI_H_R_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LI_H_R_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LI_M_LI_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LI_M_LI_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LI_M_LI_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LI_M_LR_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LI_M_LR_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LI_M_LR_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LI_M_IR_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LI_M_IR_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LI_M_IR_L_R m c0 c1 c5
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LR_H_L_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LR_H_L_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LR_H_L_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LR_H_I_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LR_H_I_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LR_H_I_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LR_H_R_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LR_H_R_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LR_H_R_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LR_M_LI_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LR_M_LI_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LR_M_LI_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LR_M_LR_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LR_M_LR_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LR_M_LR_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_LR_M_IR_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_LR_M_IR_L_I m c0 c1 c5
      · exact n7l_sAA5_M_LR_M_IR_L_R m c0 c1 c5
  · rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_IR_H_L_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_IR_H_L_L_I m c0 c1 c5
      · exact n7l_sAA5_M_IR_H_L_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_IR_H_I_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_IR_H_I_L_I m c0 c1 c5
      · exact n7l_sAA5_M_IR_H_I_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_IR_H_R_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_IR_H_R_L_I m c0 c1 c5
      · exact n7l_sAA5_M_IR_H_R_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_IR_M_LI_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_IR_M_LI_L_I m c0 c1 c5
      · exact n7l_sAA5_M_IR_M_LI_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_IR_M_LR_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_IR_M_LR_L_I m c0 c1 c5
      · exact n7l_sAA5_M_IR_M_LR_L_R m c0 c1 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact n7l_sAA5_M_IR_M_IR_L_0 m c0 c1 c5
      · exact n7l_sAA5_M_IR_M_IR_L_I m c0 c1 c5
      · exact n7l_sAA5_M_IR_M_IR_L_R m c0 c1 c5

theorem s7cert_AB0 (m : N7Model)
    {x40 x41 x42 x43 x44 : ℝ}
    (ho4 : m.t 4 ≤ x40 ∧ x40 ≤ x41 ∧ x41 ≤ x42 ∧ x42 ≤ x43 ∧ x43 ≤ x44 ∧ x44 ≤ m.t 4 + m.p)
    (hs4 : RowSig2_7 m.lam m.p (m.t 4) x40 x41 x42 x43 x44)
    (hp4 : List.Perm [x40, x41, x42, x43, x44] [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)])
    {x50 x51 x52 x53 x54 : ℝ}
    (ho5 : m.t 5 ≤ x50 ∧ x50 ≤ x51 ∧ x51 ≤ x52 ∧ x52 ≤ x53 ∧ x53 ≤ x54 ∧ x54 ≤ m.t 5 + m.p)
    (hs5 : RowSig2_7 m.lam m.p (m.t 5) x50 x51 x52 x53 x54)
    (hp5 : List.Perm [x50, x51, x52, x53, x54] [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)])
    {x00 x01 x02 x03 x04 : ℝ}
    (ho0 : m.t 0 ≤ x00 ∧ x00 ≤ x01 ∧ x01 ≤ x02 ∧ x02 ≤ x03 ∧ x03 ≤ x04 ∧ x04 ≤ m.t 0 + m.p)
    (hs0 : RowSig1_7 m.lam m.p (m.t 0) x00 x01 x02 x03 x04)
    (hp0 : List.Perm [x00, x01, x02, x03, x04] [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)])
    : False := by
  have hsp4 : ∀ z ∈ [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp5 : ∀ z ∈ [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp0 : ∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig2_7_canon_of_pos m.hlam ho4 hs4 hp4 hsp4 with c4 | c4 | c4 | c4 | c4 | c4
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_L_H_L_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_L_H_L_L_I m c4 c5 c0
      · exact n7l_sAB0_H_L_H_L_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_L_H_I_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_L_H_I_L_I m c4 c5 c0
      · exact n7l_sAB0_H_L_H_I_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_L_H_R_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_L_H_R_L_I m c4 c5 c0
      · exact n7l_sAB0_H_L_H_R_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_L_M_LI_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_L_M_LI_L_I m c4 c5 c0
      · exact n7l_sAB0_H_L_M_LI_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_L_M_LR_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_L_M_LR_L_I m c4 c5 c0
      · exact n7l_sAB0_H_L_M_LR_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_L_M_IR_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_L_M_IR_L_I m c4 c5 c0
      · exact n7l_sAB0_H_L_M_IR_L_R m c4 c5 c0
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_I_H_L_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_I_H_L_L_I m c4 c5 c0
      · exact n7l_sAB0_H_I_H_L_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_I_H_I_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_I_H_I_L_I m c4 c5 c0
      · exact n7l_sAB0_H_I_H_I_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_I_H_R_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_I_H_R_L_I m c4 c5 c0
      · exact n7l_sAB0_H_I_H_R_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_I_M_LI_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_I_M_LI_L_I m c4 c5 c0
      · exact n7l_sAB0_H_I_M_LI_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_I_M_LR_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_I_M_LR_L_I m c4 c5 c0
      · exact n7l_sAB0_H_I_M_LR_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_I_M_IR_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_I_M_IR_L_I m c4 c5 c0
      · exact n7l_sAB0_H_I_M_IR_L_R m c4 c5 c0
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_R_H_L_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_R_H_L_L_I m c4 c5 c0
      · exact n7l_sAB0_H_R_H_L_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_R_H_I_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_R_H_I_L_I m c4 c5 c0
      · exact n7l_sAB0_H_R_H_I_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_R_H_R_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_R_H_R_L_I m c4 c5 c0
      · exact n7l_sAB0_H_R_H_R_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_R_M_LI_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_R_M_LI_L_I m c4 c5 c0
      · exact n7l_sAB0_H_R_M_LI_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_R_M_LR_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_R_M_LR_L_I m c4 c5 c0
      · exact n7l_sAB0_H_R_M_LR_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_H_R_M_IR_L_0 m c4 c5 c0
      · exact n7l_sAB0_H_R_M_IR_L_I m c4 c5 c0
      · exact n7l_sAB0_H_R_M_IR_L_R m c4 c5 c0
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LI_H_L_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LI_H_L_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LI_H_L_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LI_H_I_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LI_H_I_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LI_H_I_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LI_H_R_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LI_H_R_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LI_H_R_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LI_M_LI_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LI_M_LI_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LI_M_LI_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LI_M_LR_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LI_M_LR_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LI_M_LR_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LI_M_IR_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LI_M_IR_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LI_M_IR_L_R m c4 c5 c0
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LR_H_L_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LR_H_L_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LR_H_L_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LR_H_I_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LR_H_I_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LR_H_I_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LR_H_R_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LR_H_R_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LR_H_R_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LR_M_LI_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LR_M_LI_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LR_M_LI_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LR_M_LR_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LR_M_LR_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LR_M_LR_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_LR_M_IR_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_LR_M_IR_L_I m c4 c5 c0
      · exact n7l_sAB0_M_LR_M_IR_L_R m c4 c5 c0
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_IR_H_L_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_IR_H_L_L_I m c4 c5 c0
      · exact n7l_sAB0_M_IR_H_L_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_IR_H_I_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_IR_H_I_L_I m c4 c5 c0
      · exact n7l_sAB0_M_IR_H_I_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_IR_H_R_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_IR_H_R_L_I m c4 c5 c0
      · exact n7l_sAB0_M_IR_H_R_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_IR_M_LI_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_IR_M_LI_L_I m c4 c5 c0
      · exact n7l_sAB0_M_IR_M_LI_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_IR_M_LR_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_IR_M_LR_L_I m c4 c5 c0
      · exact n7l_sAB0_M_IR_M_LR_L_R m c4 c5 c0
    · rcases msig1_7_canon_of_pos m.hlam ho0 hs0 hp0 with c0 | c0 | c0
      · exact n7l_sAB0_M_IR_M_IR_L_0 m c4 c5 c0
      · exact n7l_sAB0_M_IR_M_IR_L_I m c4 c5 c0
      · exact n7l_sAB0_M_IR_M_IR_L_R m c4 c5 c0

theorem s7cert_AB3 (m : N7Model)
    {x40 x41 x42 x43 x44 : ℝ}
    (ho4 : m.t 4 ≤ x40 ∧ x40 ≤ x41 ∧ x41 ≤ x42 ∧ x42 ≤ x43 ∧ x43 ≤ x44 ∧ x44 ≤ m.t 4 + m.p)
    (hs4 : RowSig2_7 m.lam m.p (m.t 4) x40 x41 x42 x43 x44)
    (hp4 : List.Perm [x40, x41, x42, x43, x44] [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)])
    {x50 x51 x52 x53 x54 : ℝ}
    (ho5 : m.t 5 ≤ x50 ∧ x50 ≤ x51 ∧ x51 ≤ x52 ∧ x52 ≤ x53 ∧ x53 ≤ x54 ∧ x54 ≤ m.t 5 + m.p)
    (hs5 : RowSig2_7 m.lam m.p (m.t 5) x50 x51 x52 x53 x54)
    (hp5 : List.Perm [x50, x51, x52, x53, x54] [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)])
    {x30 x31 x32 x33 x34 : ℝ}
    (ho3 : m.t 3 ≤ x30 ∧ x30 ≤ x31 ∧ x31 ≤ x32 ∧ x32 ≤ x33 ∧ x33 ≤ x34 ∧ x34 ≤ m.t 3 + m.p)
    (hs3 : RowSig1_7 m.lam m.p (m.t 3) x30 x31 x32 x33 x34)
    (hp3 : List.Perm [x30, x31, x32, x33, x34] [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)])
    : False := by
  have hsp4 : ∀ z ∈ [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp5 : ∀ z ∈ [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp3 : ∀ z ∈ [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig2_7_canon_of_pos m.hlam ho4 hs4 hp4 hsp4 with c4 | c4 | c4 | c4 | c4 | c4
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_L_H_L_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_L_H_L_L_I m c4 c5 c3
      · exact n7l_sAB3_H_L_H_L_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_L_H_I_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_L_H_I_L_I m c4 c5 c3
      · exact n7l_sAB3_H_L_H_I_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_L_H_R_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_L_H_R_L_I m c4 c5 c3
      · exact n7l_sAB3_H_L_H_R_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_L_M_LI_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_L_M_LI_L_I m c4 c5 c3
      · exact n7l_sAB3_H_L_M_LI_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_L_M_LR_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_L_M_LR_L_I m c4 c5 c3
      · exact n7l_sAB3_H_L_M_LR_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_L_M_IR_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_L_M_IR_L_I m c4 c5 c3
      · exact n7l_sAB3_H_L_M_IR_L_R m c4 c5 c3
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_I_H_L_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_I_H_L_L_I m c4 c5 c3
      · exact n7l_sAB3_H_I_H_L_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_I_H_I_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_I_H_I_L_I m c4 c5 c3
      · exact n7l_sAB3_H_I_H_I_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_I_H_R_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_I_H_R_L_I m c4 c5 c3
      · exact n7l_sAB3_H_I_H_R_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_I_M_LI_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_I_M_LI_L_I m c4 c5 c3
      · exact n7l_sAB3_H_I_M_LI_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_I_M_LR_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_I_M_LR_L_I m c4 c5 c3
      · exact n7l_sAB3_H_I_M_LR_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_I_M_IR_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_I_M_IR_L_I m c4 c5 c3
      · exact n7l_sAB3_H_I_M_IR_L_R m c4 c5 c3
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_R_H_L_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_R_H_L_L_I m c4 c5 c3
      · exact n7l_sAB3_H_R_H_L_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_R_H_I_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_R_H_I_L_I m c4 c5 c3
      · exact n7l_sAB3_H_R_H_I_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_R_H_R_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_R_H_R_L_I m c4 c5 c3
      · exact n7l_sAB3_H_R_H_R_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_R_M_LI_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_R_M_LI_L_I m c4 c5 c3
      · exact n7l_sAB3_H_R_M_LI_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_R_M_LR_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_R_M_LR_L_I m c4 c5 c3
      · exact n7l_sAB3_H_R_M_LR_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_H_R_M_IR_L_0 m c4 c5 c3
      · exact n7l_sAB3_H_R_M_IR_L_I m c4 c5 c3
      · exact n7l_sAB3_H_R_M_IR_L_R m c4 c5 c3
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LI_H_L_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LI_H_L_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LI_H_L_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LI_H_I_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LI_H_I_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LI_H_I_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LI_H_R_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LI_H_R_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LI_H_R_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LI_M_LI_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LI_M_LI_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LI_M_LI_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LI_M_LR_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LI_M_LR_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LI_M_LR_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LI_M_IR_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LI_M_IR_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LI_M_IR_L_R m c4 c5 c3
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LR_H_L_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LR_H_L_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LR_H_L_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LR_H_I_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LR_H_I_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LR_H_I_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LR_H_R_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LR_H_R_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LR_H_R_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LR_M_LI_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LR_M_LI_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LR_M_LI_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LR_M_LR_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LR_M_LR_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LR_M_LR_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_LR_M_IR_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_LR_M_IR_L_I m c4 c5 c3
      · exact n7l_sAB3_M_LR_M_IR_L_R m c4 c5 c3
  · rcases msig2_7_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_IR_H_L_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_IR_H_L_L_I m c4 c5 c3
      · exact n7l_sAB3_M_IR_H_L_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_IR_H_I_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_IR_H_I_L_I m c4 c5 c3
      · exact n7l_sAB3_M_IR_H_I_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_IR_H_R_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_IR_H_R_L_I m c4 c5 c3
      · exact n7l_sAB3_M_IR_H_R_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_IR_M_LI_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_IR_M_LI_L_I m c4 c5 c3
      · exact n7l_sAB3_M_IR_M_LI_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_IR_M_LR_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_IR_M_LR_L_I m c4 c5 c3
      · exact n7l_sAB3_M_IR_M_LR_L_R m c4 c5 c3
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · exact n7l_sAB3_M_IR_M_IR_L_0 m c4 c5 c3
      · exact n7l_sAB3_M_IR_M_IR_L_I m c4 c5 c3
      · exact n7l_sAB3_M_IR_M_IR_L_R m c4 c5 c3

end R2N4
