import Jsp000404.S7N7Defs

import Jsp000404.R1LeavesN7_16S0
import Jsp000404.R1LeavesN7_16S1
import Jsp000404.R1LeavesN7_16S10
import Jsp000404.R1LeavesN7_16S11
import Jsp000404.R1LeavesN7_16S12
import Jsp000404.R1LeavesN7_16S13
import Jsp000404.R1LeavesN7_16S14
import Jsp000404.R1LeavesN7_16S15
import Jsp000404.R1LeavesN7_16S16
import Jsp000404.R1LeavesN7_16S17
import Jsp000404.R1LeavesN7_16S18
import Jsp000404.R1LeavesN7_16S2
import Jsp000404.R1LeavesN7_16S3
import Jsp000404.R1LeavesN7_16S4
import Jsp000404.R1LeavesN7_16S5
import Jsp000404.R1LeavesN7_16S6
import Jsp000404.R1LeavesN7_16S7
import Jsp000404.R1LeavesN7_16S8
import Jsp000404.R1LeavesN7_16S9
import Jsp000404.R1LeavesN7_29S0
import Jsp000404.R1LeavesN7_29S1
import Jsp000404.R1LeavesN7_29S10
import Jsp000404.R1LeavesN7_29S11
import Jsp000404.R1LeavesN7_29S12
import Jsp000404.R1LeavesN7_29S13
import Jsp000404.R1LeavesN7_29S14
import Jsp000404.R1LeavesN7_29S15
import Jsp000404.R1LeavesN7_29S2
import Jsp000404.R1LeavesN7_29S3
import Jsp000404.R1LeavesN7_29S4
import Jsp000404.R1LeavesN7_29S5
import Jsp000404.R1LeavesN7_29S6
import Jsp000404.R1LeavesN7_29S7
import Jsp000404.R1LeavesN7_29S8
import Jsp000404.R1LeavesN7_29S9
import Jsp000404.R1LeavesN7_44S4
import Jsp000404.R1LeavesN7_44S5
import Jsp000404.R1LeavesN7_44S6
import Jsp000404.R1LeavesN7_44S7
import Jsp000404.R1LeavesN7_44S8
import Jsp000404.R1LeavesN7_44S9
import Jsp000404.R1LeavesN7_53S12
import Jsp000404.R1LeavesN7_53S13
import Jsp000404.R1LeavesN7_53S14
import Jsp000404.R1LeavesN7_53S15
import Jsp000404.R1LeavesN7_53S16
import Jsp000404.R1LeavesN7_53S17
import Jsp000404.R1LeavesN7_54S10
import Jsp000404.R1LeavesN7_54S11
import Jsp000404.R1LeavesN7_54S12
import Jsp000404.R1LeavesN7_54S13
import Jsp000404.R1LeavesN7_54S14
import Jsp000404.R1LeavesN7_54S7
import Jsp000404.R1LeavesN7_54S8
import Jsp000404.R1LeavesN7_54S9
import Jsp000404.R1LeavesN7_64S10
import Jsp000404.R1LeavesN7_64S9
import Jsp000404.R1LeavesN7_70S8
import Jsp000404.R1LeavesN7_70S9
import Jsp000404.R1LeavesN7_73S10
import Jsp000404.R1LeavesN7_73S11
import Jsp000404.R1LeavesN7_82S9
import Jsp000404.R1LeavesN7_84S8
import Jsp000404.R1LeavesN7_85S7
import Jsp000404.R1LeavesN7_87S6

namespace R2N4


theorem r1cert_T2_s2a1_s1a5 (m : N7Model)
    {x10 x11 x12 x13 x14 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ x14 ∧ x14 ≤ m.t 1 + m.p)
    (hs1 : RowSig2_7 m.lam m.p (m.t 1) x10 x11 x12 x13 x14)
    (hp1 : List.Perm [x10, x11, x12, x13, x14] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)])
    {x50 x51 x52 x53 x54 : ℝ}
    (ho5 : m.t 5 ≤ x50 ∧ x50 ≤ x51 ∧ x51 ≤ x52 ∧ x52 ≤ x53 ∧ x53 ≤ x54 ∧ x54 ≤ m.t 5 + m.p)
    (hs5 : RowSig1_7 m.lam m.p (m.t 5) x50 x51 x52 x53 x54)
    (hp5 : List.Perm [x50, x51, x52, x53, x54] [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)])
    : False := by
  have hsp1 : ∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp5 : ∀ z ∈ [(m.d 0 5), (m.d 1 5), (m.d 2 5), (m.d 3 5), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
  · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
    · exact r1l7_21_15_H_L_L_0 m c1 c5
    · exact r1l7_21_15_H_L_L_I m c1 c5
    · exact r1l7_21_15_H_L_L_R m c1 c5
  · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
    · exact r1l7_21_15_H_I_L_0 m c1 c5
    · exact r1l7_21_15_H_I_L_I m c1 c5
    · exact r1l7_21_15_H_I_L_R m c1 c5
  · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
    · exact r1l7_21_15_H_R_L_0 m c1 c5
    · exact r1l7_21_15_H_R_L_I m c1 c5
    · exact r1l7_21_15_H_R_L_R m c1 c5
  · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
    · exact r1l7_21_15_M_LI_L_0 m c1 c5
    · exact r1l7_21_15_M_LI_L_I m c1 c5
    · exact r1l7_21_15_M_LI_L_R m c1 c5
  · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
    · exact r1l7_21_M_LR m c1
    · exact r1l7_21_M_LR m c1
    · exact r1l7_21_M_LR m c1
  · rcases msig1_7_canon_of_pos m.hlam ho5 hs5 hp5 with c5 | c5 | c5
    · exact r1l7_21_15_M_IR_L_0 m c1 c5
    · exact r1l7_21_15_M_IR_L_I m c1 c5
    · exact r1l7_21_15_M_IR_L_R m c1 c5

end R2N4
