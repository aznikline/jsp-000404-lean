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


theorem r1cert_T1_s1a3_s2a4 (m : N7Model)
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
