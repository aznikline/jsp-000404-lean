import Jsp000404.S7Defs

import Jsp000404.R1LeavesN7_0

import Jsp000404.R1LeavesN7_1

import Jsp000404.R1LeavesN7_10

import Jsp000404.R1LeavesN7_11

import Jsp000404.R1LeavesN7_12

import Jsp000404.R1LeavesN7_13

import Jsp000404.R1LeavesN7_14

import Jsp000404.R1LeavesN7_15

import Jsp000404.R1LeavesN7_16

import Jsp000404.R1LeavesN7_17

import Jsp000404.R1LeavesN7_18

import Jsp000404.R1LeavesN7_19

import Jsp000404.R1LeavesN7_2

import Jsp000404.R1LeavesN7_20

import Jsp000404.R1LeavesN7_21

import Jsp000404.R1LeavesN7_22

import Jsp000404.R1LeavesN7_23

import Jsp000404.R1LeavesN7_24

import Jsp000404.R1LeavesN7_25

import Jsp000404.R1LeavesN7_26

import Jsp000404.R1LeavesN7_27

import Jsp000404.R1LeavesN7_28

import Jsp000404.R1LeavesN7_29

import Jsp000404.R1LeavesN7_3

import Jsp000404.R1LeavesN7_30

import Jsp000404.R1LeavesN7_31

import Jsp000404.R1LeavesN7_32

import Jsp000404.R1LeavesN7_33

import Jsp000404.R1LeavesN7_34

import Jsp000404.R1LeavesN7_35

import Jsp000404.R1LeavesN7_36

import Jsp000404.R1LeavesN7_37

import Jsp000404.R1LeavesN7_4

import Jsp000404.R1LeavesN7_5

import Jsp000404.R1LeavesN7_6

import Jsp000404.R1LeavesN7_7

import Jsp000404.R1LeavesN7_8

import Jsp000404.R1LeavesN7_9


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
