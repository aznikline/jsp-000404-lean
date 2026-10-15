import Jsp000404.S7N7Defs

import Jsp000404.R1LeavesN7_26S10
import Jsp000404.R1LeavesN7_26S11
import Jsp000404.R1LeavesN7_26S12
import Jsp000404.R1LeavesN7_26S13
import Jsp000404.R1LeavesN7_26S14
import Jsp000404.R1LeavesN7_26S15
import Jsp000404.R1LeavesN7_26S8
import Jsp000404.R1LeavesN7_26S9
import Jsp000404.R1LeavesN7_36S10
import Jsp000404.R1LeavesN7_36S11
import Jsp000404.R1LeavesN7_36S12
import Jsp000404.R1LeavesN7_36S7
import Jsp000404.R1LeavesN7_36S8
import Jsp000404.R1LeavesN7_36S9
import Jsp000404.R1LeavesN7_51S10
import Jsp000404.R1LeavesN7_51S11
import Jsp000404.R1LeavesN7_51S12
import Jsp000404.R1LeavesN7_51S13
import Jsp000404.R1LeavesN7_51S14
import Jsp000404.R1LeavesN7_58S5
import Jsp000404.R1LeavesN7_58S6
import Jsp000404.R1LeavesN7_58S7
import Jsp000404.R1LeavesN7_58S8
import Jsp000404.R1LeavesN7_74S8
import Jsp000404.R1LeavesN7_75S4
import Jsp000404.R1LeavesN7_75S5
import Jsp000404.R1LeavesN7_76S4
import Jsp000404.R1LeavesN7_77S6
import Jsp000404.R1LeavesN7_78S6
import Jsp000404.R1LeavesN7_84S4
import Jsp000404.R1LeavesN7_85S2
import Jsp000404.R1LeavesN7_87S2
import Jsp000404.R1LeavesN7_87S3
import Jsp000404.R1LeavesN7_87S6
import Jsp000404.R1LeavesN7_9S0
import Jsp000404.R1LeavesN7_9S1
import Jsp000404.R1LeavesN7_9S10
import Jsp000404.R1LeavesN7_9S11
import Jsp000404.R1LeavesN7_9S12
import Jsp000404.R1LeavesN7_9S13
import Jsp000404.R1LeavesN7_9S14
import Jsp000404.R1LeavesN7_9S15
import Jsp000404.R1LeavesN7_9S16
import Jsp000404.R1LeavesN7_9S17
import Jsp000404.R1LeavesN7_9S18
import Jsp000404.R1LeavesN7_9S19
import Jsp000404.R1LeavesN7_9S2
import Jsp000404.R1LeavesN7_9S20
import Jsp000404.R1LeavesN7_9S21
import Jsp000404.R1LeavesN7_9S22
import Jsp000404.R1LeavesN7_9S23
import Jsp000404.R1LeavesN7_9S24
import Jsp000404.R1LeavesN7_9S25
import Jsp000404.R1LeavesN7_9S26
import Jsp000404.R1LeavesN7_9S27
import Jsp000404.R1LeavesN7_9S3
import Jsp000404.R1LeavesN7_9S4
import Jsp000404.R1LeavesN7_9S5
import Jsp000404.R1LeavesN7_9S6
import Jsp000404.R1LeavesN7_9S7
import Jsp000404.R1LeavesN7_9S8
import Jsp000404.R1LeavesN7_9S9

namespace R2N4


theorem r1cert_T2_s1a3_s2a4 (m : N7Model)
    {x30 x31 x32 x33 x34 : ℝ}
    (ho3 : m.t 3 ≤ x30 ∧ x30 ≤ x31 ∧ x31 ≤ x32 ∧ x32 ≤ x33 ∧ x33 ≤ x34 ∧ x34 ≤ m.t 3 + m.p)
    (hs3 : RowSig1_7 m.lam m.p (m.t 3) x30 x31 x32 x33 x34)
    (hp3 : List.Perm [x30, x31, x32, x33, x34] [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)])
    {x40 x41 x42 x43 x44 : ℝ}
    (ho4 : m.t 4 ≤ x40 ∧ x40 ≤ x41 ∧ x41 ≤ x42 ∧ x42 ≤ x43 ∧ x43 ≤ x44 ∧ x44 ≤ m.t 4 + m.p)
    (hs4 : RowSig2_7 m.lam m.p (m.t 4) x40 x41 x42 x43 x44)
    (hp4 : List.Perm [x40, x41, x42, x43, x44] [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)])
    : False := by
  have hsp3 : ∀ z ∈ [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp4 : ∀ z ∈ [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
  · rcases msig2_7_canon_of_pos m.hlam ho4 hs4 hp4 hsp4 with c4 | c4 | c4 | c4 | c4 | c4
    · exact r1l7_13_24_L_0_H_L m c3 c4
    · exact r1l7_13_24_L_0_H_I m c3 c4
    · exact r1l7_13_24_L_0_H_R m c3 c4
    · exact r1l7_13_24_L_0_M_LI m c3 c4
    · exact r1l7_24_M_LR m c4
    · exact r1l7_13_24_L_0_M_IR m c3 c4
  · rcases msig2_7_canon_of_pos m.hlam ho4 hs4 hp4 hsp4 with c4 | c4 | c4 | c4 | c4 | c4
    · exact r1l7_13_24_L_I_H_L m c3 c4
    · exact r1l7_13_24_L_I_H_I m c3 c4
    · exact r1l7_13_24_L_I_H_R m c3 c4
    · exact r1l7_13_24_L_I_M_LI m c3 c4
    · exact r1l7_24_M_LR m c4
    · exact r1l7_13_24_L_I_M_IR m c3 c4
  · rcases msig2_7_canon_of_pos m.hlam ho4 hs4 hp4 hsp4 with c4 | c4 | c4 | c4 | c4 | c4
    · exact r1l7_13_24_L_R_H_L m c3 c4
    · exact r1l7_13_24_L_R_H_I m c3 c4
    · exact r1l7_13_24_L_R_H_R m c3 c4
    · exact r1l7_13_24_L_R_M_LI m c3 c4
    · exact r1l7_24_M_LR m c4
    · exact r1l7_13_24_L_R_M_IR m c3 c4

end R2N4
