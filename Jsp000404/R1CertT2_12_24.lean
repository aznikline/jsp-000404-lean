import Jsp000404.S7N7Defs

import Jsp000404.R1LeavesN7_10S0
import Jsp000404.R1LeavesN7_10S1
import Jsp000404.R1LeavesN7_10S10
import Jsp000404.R1LeavesN7_10S11
import Jsp000404.R1LeavesN7_10S12
import Jsp000404.R1LeavesN7_10S13
import Jsp000404.R1LeavesN7_10S14
import Jsp000404.R1LeavesN7_10S15
import Jsp000404.R1LeavesN7_10S16
import Jsp000404.R1LeavesN7_10S17
import Jsp000404.R1LeavesN7_10S18
import Jsp000404.R1LeavesN7_10S19
import Jsp000404.R1LeavesN7_10S2
import Jsp000404.R1LeavesN7_10S20
import Jsp000404.R1LeavesN7_10S21
import Jsp000404.R1LeavesN7_10S22
import Jsp000404.R1LeavesN7_10S23
import Jsp000404.R1LeavesN7_10S24
import Jsp000404.R1LeavesN7_10S25
import Jsp000404.R1LeavesN7_10S26
import Jsp000404.R1LeavesN7_10S3
import Jsp000404.R1LeavesN7_10S4
import Jsp000404.R1LeavesN7_10S5
import Jsp000404.R1LeavesN7_10S6
import Jsp000404.R1LeavesN7_10S7
import Jsp000404.R1LeavesN7_10S8
import Jsp000404.R1LeavesN7_10S9
import Jsp000404.R1LeavesN7_23S0
import Jsp000404.R1LeavesN7_23S1
import Jsp000404.R1LeavesN7_23S10
import Jsp000404.R1LeavesN7_23S11
import Jsp000404.R1LeavesN7_23S12
import Jsp000404.R1LeavesN7_23S13
import Jsp000404.R1LeavesN7_23S14
import Jsp000404.R1LeavesN7_23S15
import Jsp000404.R1LeavesN7_23S16
import Jsp000404.R1LeavesN7_23S17
import Jsp000404.R1LeavesN7_23S18
import Jsp000404.R1LeavesN7_23S19
import Jsp000404.R1LeavesN7_23S2
import Jsp000404.R1LeavesN7_23S3
import Jsp000404.R1LeavesN7_23S4
import Jsp000404.R1LeavesN7_23S5
import Jsp000404.R1LeavesN7_23S6
import Jsp000404.R1LeavesN7_23S7
import Jsp000404.R1LeavesN7_23S8
import Jsp000404.R1LeavesN7_23S9
import Jsp000404.R1LeavesN7_37S5
import Jsp000404.R1LeavesN7_37S6
import Jsp000404.R1LeavesN7_37S7
import Jsp000404.R1LeavesN7_37S8
import Jsp000404.R1LeavesN7_37S9
import Jsp000404.R1LeavesN7_63S3
import Jsp000404.R1LeavesN7_63S4
import Jsp000404.R1LeavesN7_63S5
import Jsp000404.R1LeavesN7_63S6
import Jsp000404.R1LeavesN7_63S7
import Jsp000404.R1LeavesN7_63S8
import Jsp000404.R1LeavesN7_68S7
import Jsp000404.R1LeavesN7_68S8
import Jsp000404.R1LeavesN7_68S9
import Jsp000404.R1LeavesN7_71S8
import Jsp000404.R1LeavesN7_78S4
import Jsp000404.R1LeavesN7_78S5
import Jsp000404.R1LeavesN7_83S7
import Jsp000404.R1LeavesN7_84S4
import Jsp000404.R1LeavesN7_86S3
import Jsp000404.R1LeavesN7_87S2
import Jsp000404.R1LeavesN7_87S6

namespace R2N4


theorem r1cert_T2_s1a2_s2a4 (m : N7Model)
    {x20 x21 x22 x23 x24 : ℝ}
    (ho2 : m.t 2 ≤ x20 ∧ x20 ≤ x21 ∧ x21 ≤ x22 ∧ x22 ≤ x23 ∧ x23 ≤ x24 ∧ x24 ≤ m.t 2 + m.p)
    (hs2 : RowSig1_7 m.lam m.p (m.t 2) x20 x21 x22 x23 x24)
    (hp2 : List.Perm [x20, x21, x22, x23, x24] [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)])
    {x40 x41 x42 x43 x44 : ℝ}
    (ho4 : m.t 4 ≤ x40 ∧ x40 ≤ x41 ∧ x41 ≤ x42 ∧ x42 ≤ x43 ∧ x43 ≤ x44 ∧ x44 ≤ m.t 4 + m.p)
    (hs4 : RowSig2_7 m.lam m.p (m.t 4) x40 x41 x42 x43 x44)
    (hp4 : List.Perm [x40, x41, x42, x43, x44] [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)])
    : False := by
  have hsp2 : ∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp4 : ∀ z ∈ [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig1_7_canon_of_pos m.hlam ho2 hs2 hp2 with c2 | c2 | c2
  · rcases msig2_7_canon_of_pos m.hlam ho4 hs4 hp4 hsp4 with c4 | c4 | c4 | c4 | c4 | c4
    · exact r1l7_12_24_L_0_H_L m c2 c4
    · exact r1l7_12_24_L_0_H_I m c2 c4
    · exact r1l7_12_24_L_0_H_R m c2 c4
    · exact r1l7_12_24_L_0_M_LI m c2 c4
    · exact r1l7_24_M_LR m c4
    · exact r1l7_12_24_L_0_M_IR m c2 c4
  · rcases msig2_7_canon_of_pos m.hlam ho4 hs4 hp4 hsp4 with c4 | c4 | c4 | c4 | c4 | c4
    · exact r1l7_12_24_L_I_H_L m c2 c4
    · exact r1l7_12_24_L_I_H_I m c2 c4
    · exact r1l7_12_24_L_I_H_R m c2 c4
    · exact r1l7_12_24_L_I_M_LI m c2 c4
    · exact r1l7_24_M_LR m c4
    · exact r1l7_12_24_L_I_M_IR m c2 c4
  · rcases msig2_7_canon_of_pos m.hlam ho4 hs4 hp4 hsp4 with c4 | c4 | c4 | c4 | c4 | c4
    · exact r1l7_12_24_L_R_H_L m c2 c4
    · exact r1l7_12_24_L_R_H_I m c2 c4
    · exact r1l7_12_24_L_R_H_R m c2 c4
    · exact r1l7_12_24_L_R_M_LI m c2 c4
    · exact r1l7_24_M_LR m c4
    · exact r1l7_12_24_L_R_M_IR m c2 c4

end R2N4
