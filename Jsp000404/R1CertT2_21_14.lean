import Jsp000404.S7N7Defs

import Jsp000404.R1LeavesN7_19S0
import Jsp000404.R1LeavesN7_19S1
import Jsp000404.R1LeavesN7_19S10
import Jsp000404.R1LeavesN7_19S11
import Jsp000404.R1LeavesN7_19S12
import Jsp000404.R1LeavesN7_19S13
import Jsp000404.R1LeavesN7_19S14
import Jsp000404.R1LeavesN7_19S15
import Jsp000404.R1LeavesN7_19S2
import Jsp000404.R1LeavesN7_19S3
import Jsp000404.R1LeavesN7_19S4
import Jsp000404.R1LeavesN7_19S5
import Jsp000404.R1LeavesN7_19S6
import Jsp000404.R1LeavesN7_19S7
import Jsp000404.R1LeavesN7_19S8
import Jsp000404.R1LeavesN7_19S9
import Jsp000404.R1LeavesN7_31S10
import Jsp000404.R1LeavesN7_31S11
import Jsp000404.R1LeavesN7_31S12
import Jsp000404.R1LeavesN7_31S13
import Jsp000404.R1LeavesN7_31S14
import Jsp000404.R1LeavesN7_31S7
import Jsp000404.R1LeavesN7_31S8
import Jsp000404.R1LeavesN7_31S9
import Jsp000404.R1LeavesN7_49S10
import Jsp000404.R1LeavesN7_49S11
import Jsp000404.R1LeavesN7_49S12
import Jsp000404.R1LeavesN7_49S13
import Jsp000404.R1LeavesN7_49S14
import Jsp000404.R1LeavesN7_49S15
import Jsp000404.R1LeavesN7_49S5
import Jsp000404.R1LeavesN7_49S6
import Jsp000404.R1LeavesN7_49S7
import Jsp000404.R1LeavesN7_49S8
import Jsp000404.R1LeavesN7_49S9
import Jsp000404.R1LeavesN7_55S10
import Jsp000404.R1LeavesN7_55S11
import Jsp000404.R1LeavesN7_55S12
import Jsp000404.R1LeavesN7_55S13
import Jsp000404.R1LeavesN7_55S14
import Jsp000404.R1LeavesN7_55S15
import Jsp000404.R1LeavesN7_55S7
import Jsp000404.R1LeavesN7_55S8
import Jsp000404.R1LeavesN7_55S9
import Jsp000404.R1LeavesN7_62S8
import Jsp000404.R1LeavesN7_62S9
import Jsp000404.R1LeavesN7_73S8
import Jsp000404.R1LeavesN7_73S9
import Jsp000404.R1LeavesN7_77S10
import Jsp000404.R1LeavesN7_77S11
import Jsp000404.R1LeavesN7_78S10
import Jsp000404.R1LeavesN7_85S6
import Jsp000404.R1LeavesN7_85S7
import Jsp000404.R1LeavesN7_86S7
import Jsp000404.R1LeavesN7_87S6

namespace R2N4


theorem r1cert_T2_s2a1_s1a4 (m : N7Model)
    {x10 x11 x12 x13 x14 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ x14 ∧ x14 ≤ m.t 1 + m.p)
    (hs1 : RowSig2_7 m.lam m.p (m.t 1) x10 x11 x12 x13 x14)
    (hp1 : List.Perm [x10, x11, x12, x13, x14] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)])
    {x40 x41 x42 x43 x44 : ℝ}
    (ho4 : m.t 4 ≤ x40 ∧ x40 ≤ x41 ∧ x41 ≤ x42 ∧ x42 ≤ x43 ∧ x43 ≤ x44 ∧ x44 ≤ m.t 4 + m.p)
    (hs4 : RowSig1_7 m.lam m.p (m.t 4) x40 x41 x42 x43 x44)
    (hp4 : List.Perm [x40, x41, x42, x43, x44] [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)])
    : False := by
  have hsp1 : ∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp4 : ∀ z ∈ [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig2_7_canon_of_pos m.hlam ho1 hs1 hp1 hsp1 with c1 | c1 | c1 | c1 | c1 | c1
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_21_14_H_L_L_0 m c1 c4
    · exact r1l7_21_14_H_L_L_I m c1 c4
    · exact r1l7_21_14_H_L_L_R m c1 c4
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_21_14_H_I_L_0 m c1 c4
    · exact r1l7_21_14_H_I_L_I m c1 c4
    · exact r1l7_21_14_H_I_L_R m c1 c4
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_21_14_H_R_L_0 m c1 c4
    · exact r1l7_21_14_H_R_L_I m c1 c4
    · exact r1l7_21_14_H_R_L_R m c1 c4
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_21_14_M_LI_L_0 m c1 c4
    · exact r1l7_21_14_M_LI_L_I m c1 c4
    · exact r1l7_21_14_M_LI_L_R m c1 c4
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_21_M_LR m c1
    · exact r1l7_21_M_LR m c1
    · exact r1l7_21_M_LR m c1
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_21_14_M_IR_L_0 m c1 c4
    · exact r1l7_21_14_M_IR_L_I m c1 c4
    · exact r1l7_21_14_M_IR_L_R m c1 c4

end R2N4
