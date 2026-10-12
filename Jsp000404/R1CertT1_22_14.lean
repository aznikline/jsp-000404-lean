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


theorem r1cert_T1_s2a2_s1a4 (m : N7Model)
    {x20 x21 x22 x23 x24 : ℝ}
    (ho2 : m.t 2 ≤ x20 ∧ x20 ≤ x21 ∧ x21 ≤ x22 ∧ x22 ≤ x23 ∧ x23 ≤ x24 ∧ x24 ≤ m.t 2 + m.p)
    (hs2 : RowSig2_7 m.lam m.p (m.t 2) x20 x21 x22 x23 x24)
    (hp2 : List.Perm [x20, x21, x22, x23, x24] [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)])
    {x40 x41 x42 x43 x44 : ℝ}
    (ho4 : m.t 4 ≤ x40 ∧ x40 ≤ x41 ∧ x41 ≤ x42 ∧ x42 ≤ x43 ∧ x43 ≤ x44 ∧ x44 ≤ m.t 4 + m.p)
    (hs4 : RowSig1_7 m.lam m.p (m.t 4) x40 x41 x42 x43 x44)
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
  rcases msig2_7_canon_of_pos m.hlam ho2 hs2 hp2 hsp2 with c2 | c2 | c2 | c2 | c2 | c2
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_22_14_H_L_L_0 m c2 c4
    · exact r1l7_22_14_H_L_L_I m c2 c4
    · exact r1l7_22_14_H_L_L_R m c2 c4
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_22_14_H_I_L_0 m c2 c4
    · exact r1l7_22_14_H_I_L_I m c2 c4
    · exact r1l7_22_14_H_I_L_R m c2 c4
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_22_14_H_R_L_0 m c2 c4
    · exact r1l7_22_14_H_R_L_I m c2 c4
    · exact r1l7_22_14_H_R_L_R m c2 c4
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_22_14_M_LI_L_0 m c2 c4
    · exact r1l7_22_14_M_LI_L_I m c2 c4
    · exact r1l7_22_14_M_LI_L_R m c2 c4
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_22_14_M_LR_L_0 m c2 c4
    · exact r1l7_22_M_LR m c2
    · exact r1l7_22_M_LR m c2
  · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
    · exact r1l7_22_14_M_IR_L_0 m c2 c4
    · exact r1l7_22_14_M_IR_L_I m c2 c4
    · exact r1l7_22_14_M_IR_L_R m c2 c4

end R2N4
