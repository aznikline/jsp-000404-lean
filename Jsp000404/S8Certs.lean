import Jsp000404.S8LeavessAA8_0
import Jsp000404.S8LeavessAA8_1
import Jsp000404.S8LeavessAA8_2
import Jsp000404.S8LeavessAB8_0
import Jsp000404.S8LeavessAB8_1
import Jsp000404.S8LeavessAB8_2
import Jsp000404.S8LeavessAB8_3
import Jsp000404.S8LeavessAB8_4
import Jsp000404.S8LeavessAB8_5
import Jsp000404.S8LeavessAB8_6
import Jsp000404.S8LeavessBT8_0
import Jsp000404.S8LeavessBT8_1
import Jsp000404.S8LeavessBT8_2
import Jsp000404.S8LeavessBT8_3
import Jsp000404.S8LeavessBT8_4
import Jsp000404.S8LeavessBT8_5
import Jsp000404.S8LeavessBT8_6
import Jsp000404.S8LeavessBT8_7
import Jsp000404.S8LeavessBT8_8

namespace R2N4


theorem s8cert_AA (m : N8Model)
    {x00 x01 x02 x03 x04 x05 : ℝ}
    (ho0 : m.t 0 ≤ x00 ∧ x00 ≤ x01 ∧ x01 ≤ x02 ∧ x02 ≤ x03 ∧ x03 ≤ x04 ∧ x04 ≤ x05 ∧ x05 ≤ m.t 0 + m.p)
    (hs0 : RowSig2_8 m.lam m.p (m.t 0) x00 x01 x02 x03 x04 x05)
    (hp0 : List.Perm [x00, x01, x02, x03, x04, x05] [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5), (m.d 0 6)])
    {x10 x11 x12 x13 x14 x15 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ x14 ∧ x14 ≤ x15 ∧ x15 ≤ m.t 1 + m.p)
    (hs1 : RowSig2_8 m.lam m.p (m.t 1) x10 x11 x12 x13 x14 x15)
    (hp1 : List.Perm [x10, x11, x12, x13, x14, x15] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5), (m.d 1 6)])
    : False := by
  have hsp0 : ∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5), (m.d 0 6)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem6or hz) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact n8_chord_bounds m (by decide)
  have hsp1 : ∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5), (m.d 1 6)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem6or hz) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact n8_chord_bounds m (by decide)
  rcases msig2_8_canon_of_pos m.hlam ho0 hs0 hp0 hsp0 with c0 | c0 | c0 | c0 | c0 | c0
  · rcases msig2_8_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · exact n8l_sAA8_H_L_H_L m c0 c1
    · exact n8l_sAA8_H_L_H_I m c0 c1
    · exact n8l_sAA8_H_L_H_R m c0 c1
    · exact n8l_sAA8_H_L_M_LI m c0 c1
    · exact n8l_sAA8_H_L_M_LR m c0 c1
    · exact n8l_sAA8_H_L_M_IR m c0 c1
  · rcases msig2_8_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · exact n8l_sAA8_H_I_H_L m c0 c1
    · exact n8l_sAA8_H_I_H_I m c0 c1
    · exact n8l_sAA8_H_I_H_R m c0 c1
    · exact n8l_sAA8_H_I_M_LI m c0 c1
    · exact n8l_sAA8_H_I_M_LR m c0 c1
    · exact n8l_sAA8_H_I_M_IR m c0 c1
  · rcases msig2_8_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · exact n8l_sAA8_H_R_H_L m c0 c1
    · exact n8l_sAA8_H_R_H_I m c0 c1
    · exact n8l_sAA8_H_R_H_R m c0 c1
    · exact n8l_sAA8_H_R_M_LI m c0 c1
    · exact n8l_sAA8_H_R_M_LR m c0 c1
    · exact n8l_sAA8_H_R_M_IR m c0 c1
  · rcases msig2_8_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · exact n8l_sAA8_M_LI_H_L m c0 c1
    · exact n8l_sAA8_M_LI_H_I m c0 c1
    · exact n8l_sAA8_M_LI_H_R m c0 c1
    · exact n8l_sAA8_M_LI_M_LI m c0 c1
    · exact n8l_sAA8_M_LI_M_LR m c0 c1
    · exact n8l_sAA8_M_LI_M_IR m c0 c1
  · rcases msig2_8_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · exact n8l_sAA8_M_LR_H_L m c0 c1
    · exact n8l_sAA8_M_LR_H_I m c0 c1
    · exact n8l_sAA8_M_LR_H_R m c0 c1
    · exact n8l_sAA8_M_LR_M_LI m c0 c1
    · exact n8l_sAA8_M_LR_M_LR m c0 c1
    · exact n8l_sAA8_M_LR_M_IR m c0 c1
  · rcases msig2_8_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
    · exact n8l_sAA8_M_IR_H_L m c0 c1
    · exact n8l_sAA8_M_IR_H_I m c0 c1
    · exact n8l_sAA8_M_IR_H_R m c0 c1
    · exact n8l_sAA8_M_IR_M_LI m c0 c1
    · exact n8l_sAA8_M_IR_M_LR m c0 c1
    · exact n8l_sAA8_M_IR_M_IR m c0 c1

theorem s8cert_BT (m : N8Model)
    {x00 x01 x02 x03 x04 x05 : ℝ}
    (ho0 : m.t 0 ≤ x00 ∧ x00 ≤ x01 ∧ x01 ≤ x02 ∧ x02 ≤ x03 ∧ x03 ≤ x04 ∧ x04 ≤ x05 ∧ x05 ≤ m.t 0 + m.p)
    (hs0 : RowSig2_8 m.lam m.p (m.t 0) x00 x01 x02 x03 x04 x05)
    (hp0 : List.Perm [x00, x01, x02, x03, x04, x05] [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5), (m.d 0 6)])
    {x60 x61 x62 x63 x64 x65 : ℝ}
    (ho6 : m.t 6 ≤ x60 ∧ x60 ≤ x61 ∧ x61 ≤ x62 ∧ x62 ≤ x63 ∧ x63 ≤ x64 ∧ x64 ≤ x65 ∧ x65 ≤ m.t 6 + m.p)
    (hs6 : RowSig2_8 m.lam m.p (m.t 6) x60 x61 x62 x63 x64 x65)
    (hp6 : List.Perm [x60, x61, x62, x63, x64, x65] [(m.d 0 6), (m.d 1 6), (m.d 2 6), (m.d 3 6), (m.d 4 6), (m.d 5 6)])
    : False := by
  have hsp0 : ∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5), (m.d 0 6)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem6or hz) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact n8_chord_bounds m (by decide)
  have hsp6 : ∀ z ∈ [(m.d 0 6), (m.d 1 6), (m.d 2 6), (m.d 3 6), (m.d 4 6), (m.d 5 6)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem6or hz) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact n8_chord_bounds m (by decide)
  rcases msig2_8_canon_of_pos m.hlam ho0 hs0 hp0 hsp0 with c0 | c0 | c0 | c0 | c0 | c0
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sBT8_H_L_H_L m c0 c6
    · exact n8l_sBT8_H_L_H_I m c0 c6
    · exact n8l_sBT8_H_L_H_R m c0 c6
    · exact n8l_sBT8_H_L_M_LI m c0 c6
    · exact n8l_sBT8_H_L_M_LR m c0 c6
    · exact n8l_sBT8_H_L_M_IR m c0 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sBT8_H_I_H_L m c0 c6
    · exact n8l_sBT8_H_I_H_I m c0 c6
    · exact n8l_sBT8_H_I_H_R m c0 c6
    · exact n8l_sBT8_H_I_M_LI m c0 c6
    · exact n8l_sBT8_H_I_M_LR m c0 c6
    · exact n8l_sBT8_H_I_M_IR m c0 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sBT8_H_R_H_L m c0 c6
    · exact n8l_sBT8_H_R_H_I m c0 c6
    · exact n8l_sBT8_H_R_H_R m c0 c6
    · exact n8l_sBT8_H_R_M_LI m c0 c6
    · exact n8l_sBT8_H_R_M_LR m c0 c6
    · exact n8l_sBT8_H_R_M_IR m c0 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sBT8_M_LI_H_L m c0 c6
    · exact n8l_sBT8_M_LI_H_I m c0 c6
    · exact n8l_sBT8_M_LI_H_R m c0 c6
    · exact n8l_sBT8_M_LI_M_LI m c0 c6
    · exact n8l_sBT8_M_LI_M_LR m c0 c6
    · exact n8l_sBT8_M_LI_M_IR m c0 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sBT8_M_LR_H_L m c0 c6
    · exact n8l_sBT8_M_LR_H_I m c0 c6
    · exact n8l_sBT8_M_LR_H_R m c0 c6
    · exact n8l_sBT8_M_LR_M_LI m c0 c6
    · exact n8l_sBT8_M_LR_M_LR m c0 c6
    · exact n8l_sBT8_M_LR_M_IR m c0 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sBT8_M_IR_H_L m c0 c6
    · exact n8l_sBT8_M_IR_H_I m c0 c6
    · exact n8l_sBT8_M_IR_H_R m c0 c6
    · exact n8l_sBT8_M_IR_M_LI m c0 c6
    · exact n8l_sBT8_M_IR_M_LR m c0 c6
    · exact n8l_sBT8_M_IR_M_IR m c0 c6

theorem s8cert_AB (m : N8Model)
    {x50 x51 x52 x53 x54 x55 : ℝ}
    (ho5 : m.t 5 ≤ x50 ∧ x50 ≤ x51 ∧ x51 ≤ x52 ∧ x52 ≤ x53 ∧ x53 ≤ x54 ∧ x54 ≤ x55 ∧ x55 ≤ m.t 5 + m.p)
    (hs5 : RowSig2_8 m.lam m.p (m.t 5) x50 x51 x52 x53 x54 x55)
    (hp5 : List.Perm [x50, x51, x52, x53, x54, x55] [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5), (m.d 5 6)])
    {x60 x61 x62 x63 x64 x65 : ℝ}
    (ho6 : m.t 6 ≤ x60 ∧ x60 ≤ x61 ∧ x61 ≤ x62 ∧ x62 ≤ x63 ∧ x63 ≤ x64 ∧ x64 ≤ x65 ∧ x65 ≤ m.t 6 + m.p)
    (hs6 : RowSig2_8 m.lam m.p (m.t 6) x60 x61 x62 x63 x64 x65)
    (hp6 : List.Perm [x60, x61, x62, x63, x64, x65] [(m.d 0 6), (m.d 1 6), (m.d 2 6), (m.d 3 6), (m.d 4 6), (m.d 5 6)])
    : False := by
  have hsp5 : ∀ z ∈ [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5), (m.d 5 6)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem6or hz) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact n8_chord_bounds m (by decide)
  have hsp6 : ∀ z ∈ [(m.d 0 6), (m.d 1 6), (m.d 2 6), (m.d 3 6), (m.d 4 6), (m.d 5 6)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem6or hz) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact n8_chord_bounds m (by decide)
  rcases msig2_8_canon_of_pos m.hlam ho5 hs5 hp5 hsp5 with c5 | c5 | c5 | c5 | c5 | c5
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sAB8_H_L_H_L m c5 c6
    · exact n8l_sAB8_H_L_H_I m c5 c6
    · exact n8l_sAB8_H_L_H_R m c5 c6
    · exact n8l_sAB8_H_L_M_LI m c5 c6
    · exact n8l_sAB8_H_L_M_LR m c5 c6
    · exact n8l_sAB8_H_L_M_IR m c5 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sAB8_H_I_H_L m c5 c6
    · exact n8l_sAB8_H_I_H_I m c5 c6
    · exact n8l_sAB8_H_I_H_R m c5 c6
    · exact n8l_sAB8_H_I_M_LI m c5 c6
    · exact n8l_sAB8_H_I_M_LR m c5 c6
    · exact n8l_sAB8_H_I_M_IR m c5 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sAB8_H_R_H_L m c5 c6
    · exact n8l_sAB8_H_R_H_I m c5 c6
    · exact n8l_sAB8_H_R_H_R m c5 c6
    · exact n8l_sAB8_H_R_M_LI m c5 c6
    · exact n8l_sAB8_H_R_M_LR m c5 c6
    · exact n8l_sAB8_H_R_M_IR m c5 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sAB8_M_LI_H_L m c5 c6
    · exact n8l_sAB8_M_LI_H_I m c5 c6
    · exact n8l_sAB8_M_LI_H_R m c5 c6
    · exact n8l_sAB8_M_LI_M_LI m c5 c6
    · exact n8l_sAB8_M_LI_M_LR m c5 c6
    · exact n8l_sAB8_M_LI_M_IR m c5 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sAB8_M_LR_H_L m c5 c6
    · exact n8l_sAB8_M_LR_H_I m c5 c6
    · exact n8l_sAB8_M_LR_H_R m c5 c6
    · exact n8l_sAB8_M_LR_M_LI m c5 c6
    · exact n8l_sAB8_M_LR_M_LR m c5 c6
    · exact n8l_sAB8_M_LR_M_IR m c5 c6
  · rcases msig2_8_canon_of_pos m.hlam ho6 hs6 hp6 hsp6 with c6 | c6 | c6 | c6 | c6 | c6
    · exact n8l_sAB8_M_IR_H_L m c5 c6
    · exact n8l_sAB8_M_IR_H_I m c5 c6
    · exact n8l_sAB8_M_IR_H_R m c5 c6
    · exact n8l_sAB8_M_IR_M_LI m c5 c6
    · exact n8l_sAB8_M_IR_M_LR m c5 c6
    · exact n8l_sAB8_M_IR_M_IR m c5 c6

end R2N4
