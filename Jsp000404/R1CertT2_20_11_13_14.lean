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

import Jsp000404.R1LeavesN7_38

import Jsp000404.R1LeavesN7_39

import Jsp000404.R1LeavesN7_4

import Jsp000404.R1LeavesN7_40

import Jsp000404.R1LeavesN7_41

import Jsp000404.R1LeavesN7_42

import Jsp000404.R1LeavesN7_43

import Jsp000404.R1LeavesN7_44

import Jsp000404.R1LeavesN7_45

import Jsp000404.R1LeavesN7_46

import Jsp000404.R1LeavesN7_47

import Jsp000404.R1LeavesN7_48

import Jsp000404.R1LeavesN7_49

import Jsp000404.R1LeavesN7_5

import Jsp000404.R1LeavesN7_50

import Jsp000404.R1LeavesN7_51

import Jsp000404.R1LeavesN7_52

import Jsp000404.R1LeavesN7_53

import Jsp000404.R1LeavesN7_54

import Jsp000404.R1LeavesN7_55

import Jsp000404.R1LeavesN7_56

import Jsp000404.R1LeavesN7_57

import Jsp000404.R1LeavesN7_58

import Jsp000404.R1LeavesN7_59

import Jsp000404.R1LeavesN7_6

import Jsp000404.R1LeavesN7_60

import Jsp000404.R1LeavesN7_61

import Jsp000404.R1LeavesN7_62

import Jsp000404.R1LeavesN7_63

import Jsp000404.R1LeavesN7_64

import Jsp000404.R1LeavesN7_65

import Jsp000404.R1LeavesN7_66

import Jsp000404.R1LeavesN7_67

import Jsp000404.R1LeavesN7_68

import Jsp000404.R1LeavesN7_69

import Jsp000404.R1LeavesN7_7

import Jsp000404.R1LeavesN7_70

import Jsp000404.R1LeavesN7_71

import Jsp000404.R1LeavesN7_72

import Jsp000404.R1LeavesN7_73

import Jsp000404.R1LeavesN7_74

import Jsp000404.R1LeavesN7_75

import Jsp000404.R1LeavesN7_76

import Jsp000404.R1LeavesN7_77

import Jsp000404.R1LeavesN7_78

import Jsp000404.R1LeavesN7_79

import Jsp000404.R1LeavesN7_8

import Jsp000404.R1LeavesN7_80

import Jsp000404.R1LeavesN7_81

import Jsp000404.R1LeavesN7_82

import Jsp000404.R1LeavesN7_83

import Jsp000404.R1LeavesN7_84

import Jsp000404.R1LeavesN7_85

import Jsp000404.R1LeavesN7_86

import Jsp000404.R1LeavesN7_87

import Jsp000404.R1LeavesN7_9


namespace R2N4


theorem r1cert_T2_s2a0_s1a1_s1a3_s1a4 (m : N7Model)
    {x00 x01 x02 x03 x04 : ℝ}
    (ho0 : m.t 0 ≤ x00 ∧ x00 ≤ x01 ∧ x01 ≤ x02 ∧ x02 ≤ x03 ∧ x03 ≤ x04 ∧ x04 ≤ m.t 0 + m.p)
    (hs0 : RowSig2_7 m.lam m.p (m.t 0) x00 x01 x02 x03 x04)
    (hp0 : List.Perm [x00, x01, x02, x03, x04] [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)])
    {x10 x11 x12 x13 x14 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ x14 ∧ x14 ≤ m.t 1 + m.p)
    (hs1 : RowSig1_7 m.lam m.p (m.t 1) x10 x11 x12 x13 x14)
    (hp1 : List.Perm [x10, x11, x12, x13, x14] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)])
    {x30 x31 x32 x33 x34 : ℝ}
    (ho3 : m.t 3 ≤ x30 ∧ x30 ≤ x31 ∧ x31 ≤ x32 ∧ x32 ≤ x33 ∧ x33 ≤ x34 ∧ x34 ≤ m.t 3 + m.p)
    (hs3 : RowSig1_7 m.lam m.p (m.t 3) x30 x31 x32 x33 x34)
    (hp3 : List.Perm [x30, x31, x32, x33, x34] [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)])
    {x40 x41 x42 x43 x44 : ℝ}
    (ho4 : m.t 4 ≤ x40 ∧ x40 ≤ x41 ∧ x41 ≤ x42 ∧ x42 ≤ x43 ∧ x43 ≤ x44 ∧ x44 ≤ m.t 4 + m.p)
    (hs4 : RowSig1_7 m.lam m.p (m.t 4) x40 x41 x42 x43 x44)
    (hp4 : List.Perm [x40, x41, x42, x43, x44] [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)])
    : False := by
  have hsp0 : ∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp1 : ∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp3 : ∀ z ∈ [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4), (m.d 3 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  have hsp4 : ∀ z ∈ [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4), (m.d 4 5)], m.lam ≤ z ∧ z < 5 * m.lam :=
    fun z hz => by
      rcases (mem5or hz) with rfl | rfl | rfl | rfl | rfl <;>
        exact n7_chord_bounds m (by decide)
  rcases msig2_7_canon_of_pos m.hlam ho0 hs0 hp0 hsp0 with c0 | c0 | c0 | c0 | c0 | c0
  · rcases msig1_7_canon_of_pos m.hlam ho1 hs1 hp1 with c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_L_L_0_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_L_L_0_L_0_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_L_L_0_L_0_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_L_L_0_L_I_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_L_L_0_L_I_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_L_L_0_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_13_14_H_L_L_R_L_0 m c0 c3 c4
        · exact r1l7_20_11_13_14_H_L_L_0_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_13_14_H_L_L_R_L_R m c0 c3 c4
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_L_L_I_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_L_L_I_L_0_L_I m c0 c1 c3 c4
        · exact r1l7_20_13_14_H_L_L_0_L_R m c0 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I m c0 c1 c3 c4
        · exact r1l7_20_14_H_L_L_R m c0 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_13_14_H_L_L_R_L_0 m c0 c3 c4
        · exact r1l7_20_11_13_14_H_L_L_I_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_13_14_H_L_L_R_L_R m c0 c3 c4
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_L_L_R_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_H_L_L_R_L_0 m c0 c1 c3
        · exact r1l7_20_11_13_H_L_L_R_L_0 m c0 c1 c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_14_H_L_L_R_L_0 m c0 c1 c4
        · exact r1l7_20_11_H_L_L_R m c0 c1
        · exact r1l7_20_11_14_H_L_L_R_L_R m c0 c1 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_14_H_L_L_R_L_0 m c0 c1 c4
        · exact r1l7_20_11_13_H_L_L_R_L_R m c0 c1 c3
        · exact r1l7_20_11_13_14_H_L_L_R_L_R_L_R m c0 c1 c3 c4
  · rcases msig1_7_canon_of_pos m.hlam ho1 hs1 hp1 with c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_I_L_0_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_H_I_L_0_L_0 m c0 c1 c3
        · exact r1l7_20_11_13_14_H_I_L_0_L_0_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_14_H_I_L_0_L_0 m c0 c1 c4
        · exact r1l7_20_11_H_I_L_0 m c0 c1
        · exact r1l7_20_11_14_H_I_L_0_L_R m c0 c1 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_I_L_0_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_I_L_0_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_H_I_L_0 m c0 c1
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_I_L_I_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_13_14_H_I_L_0_L_I m c0 c3 c4
        · exact r1l7_11_13_14_L_I_L_0_L_R m c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I m c0 c1 c3 c4
        · exact r1l7_20_14_H_I_L_R m c0 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_13_14_H_I_L_R_L_0 m c0 c3 c4
        · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R m c0 c1 c3 c4
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_I_L_R_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_H_I_L_R_L_0 m c0 c1 c3
        · exact r1l7_11_13_14_L_R_L_0_L_R m c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_11_13_14_L_R_L_I_L_0 m c1 c3 c4
        · exact r1l7_20_11_H_I_L_R m c0 c1
        · exact r1l7_20_11_13_14_H_I_L_R_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_H_I_L_R_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_I_L_R_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_I_L_R_L_R_L_R m c0 c1 c3 c4
  · rcases msig1_7_canon_of_pos m.hlam ho1 hs1 hp1 with c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_H_R_L_0 m c0 c1
        · exact r1l7_20_11_H_R_L_0 m c0 c1
        · exact r1l7_20_11_H_R_L_0 m c0 c1
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_H_R_L_0 m c0 c1
        · exact r1l7_20_11_H_R_L_0 m c0 c1
        · exact r1l7_20_11_H_R_L_0 m c0 c1
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_H_R_L_0 m c0 c1
        · exact r1l7_20_11_H_R_L_0 m c0 c1
        · exact r1l7_20_11_H_R_L_0 m c0 c1
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_13_H_R_L_0 m c0 c3
        · exact r1l7_20_13_H_R_L_0 m c0 c3
        · exact r1l7_20_13_H_R_L_0 m c0 c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_14_H_R_L_0 m c0 c4
        · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_14_H_R_L_0 m c0 c4
        · exact r1l7_20_11_13_14_H_R_L_I_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_R_L_I_L_R_L_R m c0 c1 c3 c4
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_13_H_R_L_0 m c0 c3
        · exact r1l7_20_13_H_R_L_0 m c0 c3
        · exact r1l7_20_13_H_R_L_0 m c0 c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_14_H_R_L_0 m c0 c4
        · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_14_H_R_L_0 m c0 c4
        · exact r1l7_20_11_13_14_H_R_L_R_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_H_R_L_R_L_R_L_R m c0 c1 c3 c4
  · rcases msig1_7_canon_of_pos m.hlam ho1 hs1 hp1 with c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LI_L_0_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_0_L_0_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_0_L_0_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LI_L_0_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_M_LI_L_0_L_R m c0 c1 c3
        · exact r1l7_20_11_13_14_M_LI_L_0_L_R_L_R m c0 c1 c3 c4
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LI_L_I_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_I_L_0_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_I_L_0_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_R m c0 c1 c3 c4
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LI_L_R_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_M_LI_L_R_L_0 m c0 c1 c3
        · exact r1l7_20_11_13_14_M_LI_L_R_L_0_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_14_M_LI_L_R_L_0 m c0 c1 c4
        · exact r1l7_20_11_13_M_LI_L_R_L_I m c0 c1 c3
        · exact r1l7_20_11_14_M_LI_L_R_L_R m c0 c1 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LI_L_R_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_M_LI_L_R_L_R m c0 c1 c3
        · exact r1l7_20_11_13_14_M_LI_L_R_L_R_L_R m c0 c1 c3 c4
  · rcases msig1_7_canon_of_pos m.hlam ho1 hs1 hp1 with c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_13_14_M_LR_L_0_L_0 m c0 c3 c4
        · exact r1l7_20_11_13_14_M_LR_L_0_L_0_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LR_L_0_L_0_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LR_L_0_L_I_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_14_M_LR_L_0_L_I m c0 c1 c4
        · exact r1l7_20_11_13_14_M_LR_L_0_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LR_L_0_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LR_L_0_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LR_L_0_L_R_L_R m c0 c1 c3 c4
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_13_14_M_LR_L_0_L_0 m c0 c3 c4
        · exact r1l7_20_11_13_M_LR_L_I_L_0 m c0 c1 c3
        · exact r1l7_20_13_14_M_LR_L_0_L_R m c0 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_14_M_LR_L_I_L_0 m c0 c1 c4
        · exact r1l7_20_11_14_M_LR_L_I_L_I m c0 c1 c4
        · exact r1l7_20_11_13_14_M_LR_L_I_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LR_L_I_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_M_LR_L_I_L_R m c0 c1 c3
        · exact r1l7_20_13_14_M_LR_L_R_L_R m c0 c3 c4
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LR_L_R_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_M_LR_L_R_L_0 m c0 c1 c3
        · exact r1l7_20_11_13_14_M_LR_L_R_L_0_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_14_M_LR_L_R_L_0 m c0 c1 c4
        · exact r1l7_20_11_14_M_LR_L_R_L_I m c0 c1 c4
        · exact r1l7_20_11_13_14_M_LR_L_R_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_LR_L_R_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LR_L_R_L_R_L_I m c0 c1 c3 c4
        · exact r1l7_20_11_13_14_M_LR_L_R_L_R_L_R m c0 c1 c3 c4
  · rcases msig1_7_canon_of_pos m.hlam ho1 hs1 hp1 with c1 | c1 | c1
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_IR_L_0_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_M_IR_L_0_L_0 m c0 c1 c3
        · exact r1l7_20_11_13_M_IR_L_0_L_0 m c0 c1 c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_14_M_IR_L_0_L_0 m c0 c1 c4
        · exact r1l7_20_11_M_IR_L_0 m c0 c1
        · exact r1l7_20_11_M_IR_L_0 m c0 c1
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_IR_L_0_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_M_IR_L_0 m c0 c1
        · exact r1l7_20_11_M_IR_L_0 m c0 c1
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_13_14_M_IR_L_0_L_0 m c0 c3 c4
        · exact r1l7_20_13_14_M_IR_L_0_L_I m c0 c3 c4
        · exact r1l7_20_13_14_M_IR_L_0_L_R m c0 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_14_M_IR_L_0 m c0 c4
        · exact r1l7_20_M_IR m c0
        · exact r1l7_20_14_M_IR_L_R m c0 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_IR_L_I_L_R_L_0 m c0 c1 c3 c4
        · exact r1l7_20_M_IR m c0
        · exact r1l7_20_11_13_14_M_IR_L_I_L_R_L_R m c0 c1 c3 c4
    · rcases msig1_7_canon_of_pos m.hlam ho3 hs3 hp3 with c3 | c3 | c3
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_13_14_M_IR_L_R_L_0_L_0 m c0 c1 c3 c4
        · exact r1l7_20_11_13_M_IR_L_R_L_0 m c0 c1 c3
        · exact r1l7_20_11_13_14_M_IR_L_R_L_0_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_11_14_M_IR_L_R_L_0 m c0 c1 c4
        · exact r1l7_20_11_M_IR_L_R m c0 c1
        · exact r1l7_20_11_13_14_M_IR_L_R_L_I_L_R m c0 c1 c3 c4
      · rcases msig1_7_canon_of_pos m.hlam ho4 hs4 hp4 with c4 | c4 | c4
        · exact r1l7_20_13_14_M_IR_L_R_L_0 m c0 c3 c4
        · exact r1l7_20_11_M_IR_L_R m c0 c1
        · exact r1l7_20_11_13_14_M_IR_L_R_L_R_L_R m c0 c1 c3 c4

end R2N4
