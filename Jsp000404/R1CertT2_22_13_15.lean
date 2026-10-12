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
