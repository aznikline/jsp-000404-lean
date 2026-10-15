import Jsp000404.S7N7Defs

import Jsp000404.R1LeavesN7_13S0
import Jsp000404.R1LeavesN7_13S1
import Jsp000404.R1LeavesN7_13S10
import Jsp000404.R1LeavesN7_13S11
import Jsp000404.R1LeavesN7_13S12
import Jsp000404.R1LeavesN7_13S13
import Jsp000404.R1LeavesN7_13S14
import Jsp000404.R1LeavesN7_13S15
import Jsp000404.R1LeavesN7_13S16
import Jsp000404.R1LeavesN7_13S17
import Jsp000404.R1LeavesN7_13S18
import Jsp000404.R1LeavesN7_13S19
import Jsp000404.R1LeavesN7_13S2
import Jsp000404.R1LeavesN7_13S3
import Jsp000404.R1LeavesN7_13S4
import Jsp000404.R1LeavesN7_13S5
import Jsp000404.R1LeavesN7_13S6
import Jsp000404.R1LeavesN7_13S7
import Jsp000404.R1LeavesN7_13S8
import Jsp000404.R1LeavesN7_13S9
import Jsp000404.R1LeavesN7_32S0
import Jsp000404.R1LeavesN7_32S1
import Jsp000404.R1LeavesN7_32S10
import Jsp000404.R1LeavesN7_32S11
import Jsp000404.R1LeavesN7_32S12
import Jsp000404.R1LeavesN7_32S13
import Jsp000404.R1LeavesN7_32S14
import Jsp000404.R1LeavesN7_32S15
import Jsp000404.R1LeavesN7_32S16
import Jsp000404.R1LeavesN7_32S17
import Jsp000404.R1LeavesN7_32S2
import Jsp000404.R1LeavesN7_32S3
import Jsp000404.R1LeavesN7_32S4
import Jsp000404.R1LeavesN7_32S5
import Jsp000404.R1LeavesN7_32S6
import Jsp000404.R1LeavesN7_32S7
import Jsp000404.R1LeavesN7_32S8
import Jsp000404.R1LeavesN7_32S9
import Jsp000404.R1LeavesN7_33S0
import Jsp000404.R1LeavesN7_33S1
import Jsp000404.R1LeavesN7_33S10
import Jsp000404.R1LeavesN7_33S11
import Jsp000404.R1LeavesN7_33S2
import Jsp000404.R1LeavesN7_33S3
import Jsp000404.R1LeavesN7_33S4
import Jsp000404.R1LeavesN7_33S5
import Jsp000404.R1LeavesN7_33S6
import Jsp000404.R1LeavesN7_33S7
import Jsp000404.R1LeavesN7_33S8
import Jsp000404.R1LeavesN7_33S9
import Jsp000404.R1LeavesN7_35S10
import Jsp000404.R1LeavesN7_35S11
import Jsp000404.R1LeavesN7_35S12
import Jsp000404.R1LeavesN7_35S13
import Jsp000404.R1LeavesN7_35S6
import Jsp000404.R1LeavesN7_35S7
import Jsp000404.R1LeavesN7_35S8
import Jsp000404.R1LeavesN7_35S9
import Jsp000404.R1LeavesN7_42S10
import Jsp000404.R1LeavesN7_42S11
import Jsp000404.R1LeavesN7_42S12
import Jsp000404.R1LeavesN7_42S13
import Jsp000404.R1LeavesN7_42S14
import Jsp000404.R1LeavesN7_42S9
import Jsp000404.R1LeavesN7_44S10
import Jsp000404.R1LeavesN7_44S11
import Jsp000404.R1LeavesN7_44S12
import Jsp000404.R1LeavesN7_44S13
import Jsp000404.R1LeavesN7_61S12
import Jsp000404.R1LeavesN7_61S13
import Jsp000404.R1LeavesN7_62S10
import Jsp000404.R1LeavesN7_62S11
import Jsp000404.R1LeavesN7_65S11
import Jsp000404.R1LeavesN7_65S12
import Jsp000404.R1LeavesN7_65S13
import Jsp000404.R1LeavesN7_66S13
import Jsp000404.R1LeavesN7_66S14
import Jsp000404.R1LeavesN7_67S11
import Jsp000404.R1LeavesN7_67S12
import Jsp000404.R1LeavesN7_72S10
import Jsp000404.R1LeavesN7_72S11
import Jsp000404.R1LeavesN7_75S10
import Jsp000404.R1LeavesN7_75S11
import Jsp000404.R1LeavesN7_75S12
import Jsp000404.R1LeavesN7_75S13
import Jsp000404.R1LeavesN7_75S9
import Jsp000404.R1LeavesN7_76S10
import Jsp000404.R1LeavesN7_76S9
import Jsp000404.R1LeavesN7_80S11
import Jsp000404.R1LeavesN7_82S10
import Jsp000404.R1LeavesN7_83S10
import Jsp000404.R1LeavesN7_83S9
import Jsp000404.R1LeavesN7_85S7
import Jsp000404.R1LeavesN7_86S7
import Jsp000404.R1LeavesN7_86S8
import Jsp000404.R1LeavesN7_87S6

namespace R2N4


theorem r1cert_T2_s2a2_s1a3_s1a5 (m : N7Model)
    {x20 x21 x22 x23 x24 : ℝ}
    (ho2 : m.t 2 ≤ x20 ∧ x20 ≤ x21 ∧ x21 ≤ x22 ∧ x22 ≤ x23 ∧ x23 ≤ x24 ∧ x24 ≤ m.t 2 + m.p)
    (hs2 : RowSig2_7 m.lam m.p (m.t 2) x20 x21 x22 x23 x24)
    (hp2 : List.Perm [x20, x21, x22, x23, x24] [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)])
    {x30 x31 x32 x33 x34 : ℝ}
    (ho3 : m.t 3 ≤ x30 ∧ x30 ≤ x31 ∧ x31 ≤ x32 ∧ x32 ≤ x33 ∧ x33 ≤ x34 ∧ x34 ≤ m.t 3 + m.p)
    (hs3 : RowSig1_7 m.lam m.p (m.t 3) x30 x31 x32 x33 x34)
    (hp3 : List.Perm [x30, x31, x32, x33, x34] [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)])
    {x50 x51 x52 x53 x54 : ℝ}
    (ho5 : m.t 5 ≤ x50 ∧ x50 ≤ x51 ∧ x51 ≤ x52 ∧ x52 ≤ x53 ∧ x53 ≤ x54 ∧ x54 ≤ m.t 5 + m.p)
    (hs5 : RowSig1_7 m.lam m.p (m.t 5) x50 x51 x52 x53 x54)
    (hp5 : List.Perm [x50, x51, x52, x53, x54] [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)])
    : False := by
  have hsp2 : ∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp3 : ∀ z ∈ [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp5 : ∀ z ∈ [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig2_7_canon_of_pos m.hlam ho2 hs2 hp2 hsp2 with c2 | c2 | c2 | c2 | c2 | c2
  · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_H_L_L_0_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_H_L_L_0_L_I m c2 c3 c5
      · exact r1l7_22_15_H_L_L_R m c2 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_H_L_L_I_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_H_L_L_I_L_I m c2 c3 c5
      · exact r1l7_22_15_H_L_L_R m c2 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_H_L_L_R_L_0 m c2 c3 c5
      · exact r1l7_22_13_H_L_L_R m c2 c3
      · exact r1l7_22_13_H_L_L_R m c2 c3
  · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_H_I_L_0_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_H_I_L_0_L_I m c2 c3 c5
      · exact r1l7_22_13_15_H_I_L_0_L_R m c2 c3 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_H_I_L_I_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_H_I_L_I_L_I m c2 c3 c5
      · exact r1l7_22_15_H_I_L_R m c2 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_H_I_L_R_L_0 m c2 c3 c5
      · exact r1l7_22_13_H_I_L_R m c2 c3
      · exact r1l7_22_13_15_H_I_L_R_L_R m c2 c3 c5
  · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_H_R_L_0 m c2 c3
      · exact r1l7_22_13_H_R_L_0 m c2 c3
      · exact r1l7_22_13_H_R_L_0 m c2 c3
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_15_H_R_L_0 m c2 c5
      · exact r1l7_22_13_15_H_R_L_I_L_I m c2 c3 c5
      · exact r1l7_22_13_15_H_R_L_I_L_R m c2 c3 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_15_H_R_L_0 m c2 c5
      · exact r1l7_22_13_15_H_R_L_R_L_I m c2 c3 c5
      · exact r1l7_22_13_15_H_R_L_R_L_R m c2 c3 c5
  · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_M_LI_L_0_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_M_LI_L_0_L_I m c2 c3 c5
      · exact r1l7_22_13_15_M_LI_L_0_L_R m c2 c3 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_M_LI_L_I_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_M_LI_L_I_L_I m c2 c3 c5
      · exact r1l7_22_15_M_LI_L_R m c2 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_M_LI_L_R_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_M_LI_L_R_L_I m c2 c3 c5
      · exact r1l7_22_13_15_M_LI_L_R_L_R m c2 c3 c5
  · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_M_LR m c2
      · exact r1l7_22_M_LR m c2
      · exact r1l7_22_M_LR m c2
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_M_LR m c2
      · exact r1l7_22_M_LR m c2
      · exact r1l7_22_M_LR m c2
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_M_LR m c2
      · exact r1l7_22_M_LR m c2
      · exact r1l7_22_M_LR m c2
  · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_M_IR_L_0_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_M_IR_L_0_L_I m c2 c3 c5
      · exact r1l7_22_13_15_M_IR_L_0_L_R m c2 c3 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_M_IR_L_I_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_M_IR_L_I_L_I m c2 c3 c5
      · exact r1l7_22_13_15_M_IR_L_I_L_R m c2 c3 c5
    · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
      · exact r1l7_22_13_15_M_IR_L_R_L_0 m c2 c3 c5
      · exact r1l7_22_13_15_M_IR_L_R_L_I m c2 c3 c5
      · exact r1l7_22_13_15_M_IR_L_R_L_R m c2 c3 c5

end R2N4
