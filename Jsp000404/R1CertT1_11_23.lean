import Jsp000404.S7N7Defs

import Jsp000404.R1LeavesN7_39S10
import Jsp000404.R1LeavesN7_39S5
import Jsp000404.R1LeavesN7_39S6
import Jsp000404.R1LeavesN7_39S7
import Jsp000404.R1LeavesN7_39S8
import Jsp000404.R1LeavesN7_39S9
import Jsp000404.R1LeavesN7_4S0
import Jsp000404.R1LeavesN7_4S1
import Jsp000404.R1LeavesN7_4S10
import Jsp000404.R1LeavesN7_4S11
import Jsp000404.R1LeavesN7_4S12
import Jsp000404.R1LeavesN7_4S13
import Jsp000404.R1LeavesN7_4S14
import Jsp000404.R1LeavesN7_4S15
import Jsp000404.R1LeavesN7_4S16
import Jsp000404.R1LeavesN7_4S17
import Jsp000404.R1LeavesN7_4S18
import Jsp000404.R1LeavesN7_4S19
import Jsp000404.R1LeavesN7_4S2
import Jsp000404.R1LeavesN7_4S20
import Jsp000404.R1LeavesN7_4S21
import Jsp000404.R1LeavesN7_4S22
import Jsp000404.R1LeavesN7_4S23
import Jsp000404.R1LeavesN7_4S24
import Jsp000404.R1LeavesN7_4S25
import Jsp000404.R1LeavesN7_4S26
import Jsp000404.R1LeavesN7_4S27
import Jsp000404.R1LeavesN7_4S28
import Jsp000404.R1LeavesN7_4S29
import Jsp000404.R1LeavesN7_4S3
import Jsp000404.R1LeavesN7_4S30
import Jsp000404.R1LeavesN7_4S31
import Jsp000404.R1LeavesN7_4S4
import Jsp000404.R1LeavesN7_4S5
import Jsp000404.R1LeavesN7_4S6
import Jsp000404.R1LeavesN7_4S7
import Jsp000404.R1LeavesN7_4S8
import Jsp000404.R1LeavesN7_4S9
import Jsp000404.R1LeavesN7_54S0
import Jsp000404.R1LeavesN7_54S1
import Jsp000404.R1LeavesN7_54S2
import Jsp000404.R1LeavesN7_54S3
import Jsp000404.R1LeavesN7_59S5
import Jsp000404.R1LeavesN7_59S6
import Jsp000404.R1LeavesN7_59S7
import Jsp000404.R1LeavesN7_65S4
import Jsp000404.R1LeavesN7_65S5
import Jsp000404.R1LeavesN7_65S6
import Jsp000404.R1LeavesN7_81S5
import Jsp000404.R1LeavesN7_82S5
import Jsp000404.R1LeavesN7_84S3
import Jsp000404.R1LeavesN7_87S2
import Jsp000404.R1LeavesN7_87S6

namespace R2N4


theorem r1cert_T1_s1a1_s2a3 (m : N7Model)
    {x10 x11 x12 x13 x14 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ x14 ∧ x14 ≤ m.t 1 + m.p)
    (hs1 : RowSig1_7 m.lam m.p (m.t 1) x10 x11 x12 x13 x14)
    (hp1 : List.Perm [x10, x11, x12, x13, x14] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)])
    {x30 x31 x32 x33 x34 : ℝ}
    (ho3 : m.t 3 ≤ x30 ∧ x30 ≤ x31 ∧ x31 ≤ x32 ∧ x32 ≤ x33 ∧ x33 ≤ x34 ∧ x34 ≤ m.t 3 + m.p)
    (hs3 : RowSig2_7 m.lam m.p (m.t 3) x30 x31 x32 x33 x34)
    (hp3 : List.Perm [x30, x31, x32, x33, x34] [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)])
    : False := by
  have hsp1 : ∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp3 : ∀ z ∈ [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig1_7_canon_of_pos m.hlam ho1 hs1 hp1 with c1 | c1 | c1
  · rcases msig2_7_canon_of_pos m.hlam ho3 hs3 hp3 hsp3 with c3 | c3 | c3 | c3 | c3 | c3
    · exact r1l7_11_23_L_0_H_L m c1 c3
    · exact r1l7_11_23_L_0_H_I m c1 c3
    · exact r1l7_11_23_L_0_H_R m c1 c3
    · exact r1l7_11_23_L_0_M_LI m c1 c3
    · exact r1l7_23_M_LR m c3
    · exact r1l7_11_23_L_0_M_IR m c1 c3
  · rcases msig2_7_canon_of_pos m.hlam ho3 hs3 hp3 hsp3 with c3 | c3 | c3 | c3 | c3 | c3
    · exact r1l7_11_23_L_I_H_L m c1 c3
    · exact r1l7_11_23_L_I_H_I m c1 c3
    · exact r1l7_11_23_L_I_H_R m c1 c3
    · exact r1l7_11_23_L_I_M_LI m c1 c3
    · exact r1l7_23_M_LR m c3
    · exact r1l7_11_23_L_I_M_IR m c1 c3
  · rcases msig2_7_canon_of_pos m.hlam ho3 hs3 hp3 hsp3 with c3 | c3 | c3 | c3 | c3 | c3
    · exact r1l7_11_23_L_R_H_L m c1 c3
    · exact r1l7_11_23_L_R_H_I m c1 c3
    · exact r1l7_11_23_L_R_H_R m c1 c3
    · exact r1l7_11_23_L_R_M_LI m c1 c3
    · exact r1l7_23_M_LR m c3
    · exact r1l7_11_23_L_R_M_IR m c1 c3

end R2N4
