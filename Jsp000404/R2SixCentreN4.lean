import Jsp000404.N4LeavesPA
import Jsp000404.N4LeavesPB1
import Jsp000404.N4LeavesPB2
import Jsp000404.N4LeavesPE1
import Jsp000404.N4LeavesPE2
import Jsp000404.N4LeavesTA1
import Jsp000404.N4LeavesTA2
import Jsp000404.N4LeavesTA3
import Jsp000404.N4LeavesTA4
import Jsp000404.N4LeavesTB1
import Jsp000404.N4LeavesTB10
import Jsp000404.N4LeavesTB11
import Jsp000404.N4LeavesTB12
import Jsp000404.N4LeavesTB2
import Jsp000404.N4LeavesTB3
import Jsp000404.N4LeavesTB4
import Jsp000404.N4LeavesTB5
import Jsp000404.N4LeavesTB6
import Jsp000404.N4LeavesTB7
import Jsp000404.N4LeavesTB8
import Jsp000404.N4LeavesTB9

namespace R2N4


theorem n4cert_pair_A (m : N4Model)
    {x10 x11 x12 x13 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ m.t 1 + m.p)
    (hs1 : RowSig2 m.lam m.p (m.t 1) x10 x11 x12 x13)
    (hp1 : List.Perm [x10, x11, x12, x13] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4)])
    {x30 x31 x32 x33 : ℝ}
    (ho3 : m.t 3 ≤ x30 ∧ x30 ≤ x31 ∧ x31 ≤ x32 ∧ x32 ≤ x33 ∧ x33 ≤ m.t 3 + m.p)
    (hs3 : RowSig1 m.lam m.p (m.t 3) x30 x31 x32 x33)
    (hp3 : List.Perm [x30, x31, x32, x33] [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4)])
    : False := by
  rcases hs1 with s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_0_0 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_0_1 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_0_2 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_0_3 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_0_4 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_1_0 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_1_1 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_1_2 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_1_3 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_1_4 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_2_0 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_2_1 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_2_2 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_2_3 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_2_4 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_3_0 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_3_1 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_3_2 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_3_3 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_3_4 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_4_0 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_4_1 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_4_2 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_4_3 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_4_4 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_5_0 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_5_1 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_5_2 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_5_3 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_5_4 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_6_0 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_6_1 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_6_2 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_6_3 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_6_4 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_7_0 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_7_1 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_7_2 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_7_3 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_7_4 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_8_0 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_8_1 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_8_2 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_8_3 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_8_4 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_9_0 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_9_1 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_9_2 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_9_3 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_9_4 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_10_0 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_10_1 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_10_2 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_10_3 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_10_4 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_11_0 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_11_1 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_11_2 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_11_3 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_11_4 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_12_0 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_12_1 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_12_2 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_12_3 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_12_4 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_13_0 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_13_1 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_13_2 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_13_3 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_13_4 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3
    · exact n4l_pA_14_0 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_14_1 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_14_2 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_14_3 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pA_14_4 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho3 s3 hp3)

theorem n4cert_pair_B (m : N4Model)
    {x10 x11 x12 x13 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ m.t 1 + m.p)
    (hs1 : RowSig1 m.lam m.p (m.t 1) x10 x11 x12 x13)
    (hp1 : List.Perm [x10, x11, x12, x13] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4)])
    {x30 x31 x32 x33 : ℝ}
    (ho3 : m.t 3 ≤ x30 ∧ x30 ≤ x31 ∧ x31 ≤ x32 ∧ x32 ≤ x33 ∧ x33 ≤ m.t 3 + m.p)
    (hs3 : RowSig2 m.lam m.p (m.t 3) x30 x31 x32 x33)
    (hp3 : List.Perm [x30, x31, x32, x33] [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4)])
    : False := by
  rcases hs1 with s1 | s1 | s1 | s1 | s1
  · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
    · exact n4l_pB_0_0 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_1 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_2 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_3 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_4 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_5 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_6 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_7 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_8 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_9 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_10 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_11 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_12 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_13 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_0_14 m (msig1_0_of_pos m.hlam ho1 s1 hp1) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
    · exact n4l_pB_1_0 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_1 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_2 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_3 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_4 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_5 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_6 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_7 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_8 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_9 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_10 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_11 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_12 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_13 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_1_14 m (msig1_1_of_pos m.hlam ho1 s1 hp1) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
    · exact n4l_pB_2_0 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_1 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_2 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_3 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_4 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_5 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_6 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_7 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_8 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_9 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_10 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_11 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_12 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_13 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_2_14 m (msig1_2_of_pos m.hlam ho1 s1 hp1) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
    · exact n4l_pB_3_0 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_1 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_2 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_3 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_4 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_5 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_6 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_7 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_8 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_9 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_10 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_11 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_12 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_13 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_3_14 m (msig1_3_of_pos m.hlam ho1 s1 hp1) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
    · exact n4l_pB_4_0 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_0_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_1 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_2 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_3 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_4 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_5 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_6 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_7 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_8 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_9 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_10 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_11 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_12 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_13 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
    · exact n4l_pB_4_14 m (msig1_4_of_pos m.hlam ho1 s1 hp1) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)

theorem n4cert_triple_A (m : N4Model)
    {x10 x11 x12 x13 : ℝ}
    (ho1 : m.t 1 ≤ x10 ∧ x10 ≤ x11 ∧ x11 ≤ x12 ∧ x12 ≤ x13 ∧ x13 ≤ m.t 1 + m.p)
    (hs1 : RowSig2 m.lam m.p (m.t 1) x10 x11 x12 x13)
    (hp1 : List.Perm [x10, x11, x12, x13] [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4)])
    {x20 x21 x22 x23 : ℝ}
    (ho2 : m.t 2 ≤ x20 ∧ x20 ≤ x21 ∧ x21 ≤ x22 ∧ x22 ≤ x23 ∧ x23 ≤ m.t 2 + m.p)
    (hs2 : RowSig1 m.lam m.p (m.t 2) x20 x21 x22 x23)
    (hp2 : List.Perm [x20, x21, x22, x23] [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4)])
    {x40 x41 x42 x43 : ℝ}
    (ho4 : m.t 4 ≤ x40 ∧ x40 ≤ x41 ∧ x41 ≤ x42 ∧ x42 ≤ x43 ∧ x43 ≤ m.t 4 + m.p)
    (hs4 : RowSig1 m.lam m.p (m.t 4) x40 x41 x42 x43)
    (hp4 : List.Perm [x40, x41, x42, x43] [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4)])
    : False := by
  rcases hs1 with s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_0_0_0 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_0_1 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_0_2 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_0_3 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_0_4 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_0_1_0 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_1_1 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_1_2 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_1_3 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_1_4 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_0_2_0 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_2_1 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_2_2 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_2_3 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_2_4 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_0_3_0 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_3_1 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_3_2 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_3_3 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_3_4 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_0_4_0 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_4_1 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_4_2 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_4_3 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_0_4_4 m (msig2_0_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_1_0_0 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_0_1 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_0_2 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_0_3 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_0_4 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_1_1_0 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_1_1 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_1_2 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_1_3 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_1_4 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_1_2_0 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_2_1 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_2_2 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_2_3 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_2_4 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_1_3_0 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_3_1 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_3_2 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_3_3 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_3_4 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_1_4_0 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_4_1 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_4_2 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_4_3 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_1_4_4 m (msig2_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_2_0_0 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_0_1 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_0_2 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_0_3 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_0_4 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_2_1_0 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_1_1 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_1_2 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_1_3 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_1_4 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_2_2_0 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_2_1 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_2_2 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_2_3 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_2_4 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_2_3_0 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_3_1 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_3_2 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_3_3 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_3_4 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_2_4_0 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_4_1 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_4_2 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_4_3 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_2_4_4 m (msig2_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_3_0_0 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_0_1 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_0_2 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_0_3 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_0_4 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_3_1_0 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_1_1 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_1_2 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_1_3 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_1_4 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_3_2_0 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_2_1 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_2_2 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_2_3 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_2_4 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_3_3_0 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_3_1 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_3_2 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_3_3 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_3_4 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_3_4_0 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_4_1 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_4_2 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_4_3 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_3_4_4 m (msig2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_4_0_0 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_0_1 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_0_2 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_0_3 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_0_4 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_4_1_0 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_1_1 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_1_2 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_1_3 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_1_4 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_4_2_0 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_2_1 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_2_2 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_2_3 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_2_4 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_4_3_0 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_3_1 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_3_2 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_3_3 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_3_4 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_4_4_0 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_4_1 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_4_2 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_4_3 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_4_4_4 m (msig2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_5_0_0 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_0_1 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_0_2 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_0_3 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_0_4 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_5_1_0 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_1_1 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_1_2 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_1_3 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_1_4 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_5_2_0 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_2_1 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_2_2 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_2_3 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_2_4 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_5_3_0 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_3_1 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_3_2 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_3_3 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_3_4 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_5_4_0 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_4_1 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_4_2 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_4_3 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_5_4_4 m (msig2_0_1_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_6_0_0 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_0_1 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_0_2 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_0_3 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_0_4 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_6_1_0 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_1_1 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_1_2 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_1_3 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_1_4 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_6_2_0 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_2_1 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_2_2 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_2_3 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_2_4 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_6_3_0 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_3_1 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_3_2 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_3_3 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_3_4 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_6_4_0 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_4_1 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_4_2 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_4_3 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_6_4_4 m (msig2_0_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_7_0_0 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_0_1 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_0_2 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_0_3 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_0_4 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_7_1_0 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_1_1 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_1_2 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_1_3 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_1_4 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_7_2_0 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_2_1 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_2_2 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_2_3 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_2_4 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_7_3_0 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_3_1 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_3_2 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_3_3 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_3_4 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_7_4_0 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_4_1 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_4_2 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_4_3 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_7_4_4 m (msig2_0_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_8_0_0 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_0_1 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_0_2 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_0_3 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_0_4 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_8_1_0 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_1_1 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_1_2 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_1_3 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_1_4 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_8_2_0 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_2_1 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_2_2 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_2_3 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_2_4 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_8_3_0 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_3_1 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_3_2 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_3_3 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_3_4 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_8_4_0 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_4_1 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_4_2 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_4_3 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_8_4_4 m (msig2_0_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_9_0_0 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_0_1 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_0_2 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_0_3 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_0_4 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_9_1_0 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_1_1 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_1_2 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_1_3 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_1_4 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_9_2_0 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_2_1 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_2_2 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_2_3 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_2_4 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_9_3_0 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_3_1 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_3_2 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_3_3 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_3_4 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_9_4_0 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_4_1 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_4_2 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_4_3 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_9_4_4 m (msig2_1_2_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_10_0_0 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_0_1 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_0_2 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_0_3 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_0_4 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_10_1_0 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_1_1 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_1_2 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_1_3 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_1_4 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_10_2_0 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_2_1 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_2_2 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_2_3 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_2_4 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_10_3_0 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_3_1 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_3_2 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_3_3 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_3_4 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_10_4_0 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_4_1 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_4_2 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_4_3 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_10_4_4 m (msig2_1_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_11_0_0 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_0_1 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_0_2 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_0_3 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_0_4 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_11_1_0 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_1_1 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_1_2 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_1_3 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_1_4 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_11_2_0 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_2_1 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_2_2 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_2_3 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_2_4 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_11_3_0 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_3_1 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_3_2 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_3_3 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_3_4 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_11_4_0 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_4_1 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_4_2 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_4_3 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_11_4_4 m (msig2_1_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_12_0_0 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_0_1 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_0_2 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_0_3 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_0_4 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_12_1_0 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_1_1 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_1_2 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_1_3 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_1_4 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_12_2_0 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_2_1 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_2_2 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_2_3 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_2_4 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_12_3_0 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_3_1 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_3_2 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_3_3 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_3_4 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_12_4_0 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_4_1 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_4_2 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_4_3 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_12_4_4 m (msig2_2_3_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_13_0_0 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_0_1 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_0_2 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_0_3 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_0_4 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_13_1_0 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_1_1 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_1_2 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_1_3 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_1_4 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_13_2_0 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_2_1 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_2_2 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_2_3 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_2_4 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_13_3_0 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_3_1 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_3_2 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_3_3 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_3_4 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_13_4_0 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_4_1 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_4_2 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_4_3 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_13_4_4 m (msig2_2_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_14_0_0 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_0_1 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_0_2 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_0_3 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_0_4 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_14_1_0 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_1_1 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_1_2 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_1_3 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_1_4 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_14_2_0 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_2_1 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_2_2 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_2_3 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_2_4 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_14_3_0 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_3_1 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_3_2 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_3_3 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_3_4 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)
    · rcases hs4 with s4 | s4 | s4 | s4 | s4
      · exact n4l_tA_14_4_0 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_0_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_4_1 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_1_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_4_2 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_2_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_4_3 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_3_of_pos m.hlam ho4 s4 hp4)
      · exact n4l_tA_14_4_4 m (msig2_3_4_of_pos m.hlam ho1 s1 hp1) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig1_4_of_pos m.hlam ho4 s4 hp4)

theorem n4cert_triple_B (m : N4Model)
    {x00 x01 x02 x03 : ℝ}
    (ho0 : m.t 0 ≤ x00 ∧ x00 ≤ x01 ∧ x01 ≤ x02 ∧ x02 ≤ x03 ∧ x03 ≤ m.t 0 + m.p)
    (hs0 : RowSig1 m.lam m.p (m.t 0) x00 x01 x02 x03)
    (hp0 : List.Perm [x00, x01, x02, x03] [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4)])
    {x20 x21 x22 x23 : ℝ}
    (ho2 : m.t 2 ≤ x20 ∧ x20 ≤ x21 ∧ x21 ≤ x22 ∧ x22 ≤ x23 ∧ x23 ≤ m.t 2 + m.p)
    (hs2 : RowSig1 m.lam m.p (m.t 2) x20 x21 x22 x23)
    (hp2 : List.Perm [x20, x21, x22, x23] [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4)])
    {x30 x31 x32 x33 : ℝ}
    (ho3 : m.t 3 ≤ x30 ∧ x30 ≤ x31 ∧ x31 ≤ x32 ∧ x32 ≤ x33 ∧ x33 ≤ m.t 3 + m.p)
    (hs3 : RowSig2 m.lam m.p (m.t 3) x30 x31 x32 x33)
    (hp3 : List.Perm [x30, x31, x32, x33] [(m.d 0 3), (m.d 1 3), (m.d 2 3), (m.d 3 4)])
    : False := by
  rcases hs0 with s0 | s0 | s0 | s0 | s0
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_0_0_0 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_1 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_2 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_3 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_4 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_5 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_6 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_7 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_8 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_9 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_10 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_11 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_12 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_13 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_0_14 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_0_1_0 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_1 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_2 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_3 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_4 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_5 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_6 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_7 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_8 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_9 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_10 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_11 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_12 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_13 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_1_14 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_0_2_0 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_1 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_2 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_3 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_4 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_5 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_6 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_7 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_8 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_9 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_10 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_11 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_12 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_13 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_2_14 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_0_3_0 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_1 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_2 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_3 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_4 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_5 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_6 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_7 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_8 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_9 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_10 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_11 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_12 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_13 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_3_14 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_0_4_0 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_1 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_2 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_3 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_4 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_5 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_6 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_7 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_8 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_9 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_10 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_11 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_12 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_13 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_0_4_14 m (msig1_0_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_1_0_0 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_1 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_2 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_3 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_4 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_5 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_6 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_7 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_8 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_9 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_10 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_11 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_12 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_13 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_0_14 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_1_1_0 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_1 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_2 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_3 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_4 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_5 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_6 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_7 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_8 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_9 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_10 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_11 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_12 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_13 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_1_14 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_1_2_0 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_1 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_2 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_3 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_4 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_5 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_6 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_7 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_8 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_9 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_10 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_11 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_12 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_13 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_2_14 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_1_3_0 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_1 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_2 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_3 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_4 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_5 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_6 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_7 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_8 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_9 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_10 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_11 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_12 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_13 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_3_14 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_1_4_0 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_1 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_2 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_3 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_4 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_5 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_6 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_7 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_8 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_9 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_10 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_11 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_12 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_13 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_1_4_14 m (msig1_1_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_2_0_0 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_1 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_2 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_3 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_4 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_5 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_6 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_7 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_8 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_9 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_10 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_11 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_12 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_13 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_0_14 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_2_1_0 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_1 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_2 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_3 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_4 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_5 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_6 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_7 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_8 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_9 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_10 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_11 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_12 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_13 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_1_14 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_2_2_0 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_1 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_2 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_3 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_4 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_5 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_6 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_7 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_8 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_9 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_10 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_11 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_12 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_13 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_2_14 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_2_3_0 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_1 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_2 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_3 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_4 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_5 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_6 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_7 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_8 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_9 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_10 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_11 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_12 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_13 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_3_14 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_2_4_0 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_1 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_2 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_3 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_4 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_5 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_6 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_7 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_8 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_9 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_10 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_11 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_12 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_13 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_2_4_14 m (msig1_2_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_3_0_0 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_1 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_2 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_3 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_4 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_5 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_6 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_7 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_8 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_9 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_10 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_11 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_12 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_13 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_0_14 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_3_1_0 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_1 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_2 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_3 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_4 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_5 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_6 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_7 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_8 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_9 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_10 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_11 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_12 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_13 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_1_14 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_3_2_0 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_1 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_2 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_3 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_4 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_5 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_6 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_7 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_8 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_9 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_10 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_11 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_12 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_13 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_2_14 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_3_3_0 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_1 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_2 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_3 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_4 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_5 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_6 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_7 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_8 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_9 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_10 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_11 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_12 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_13 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_3_14 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_3_4_0 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_1 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_2 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_3 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_4 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_5 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_6 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_7 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_8 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_9 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_10 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_11 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_12 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_13 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_3_4_14 m (msig1_3_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
  · rcases hs2 with s2 | s2 | s2 | s2 | s2
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_4_0_0 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_1 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_2 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_3 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_4 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_5 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_6 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_7 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_8 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_9 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_10 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_11 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_12 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_13 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_0_14 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_0_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_4_1_0 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_1 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_2 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_3 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_4 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_5 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_6 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_7 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_8 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_9 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_10 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_11 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_12 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_13 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_1_14 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_1_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_4_2_0 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_1 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_2 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_3 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_4 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_5 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_6 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_7 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_8 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_9 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_10 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_11 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_12 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_13 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_2_14 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_2_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_4_3_0 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_1 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_2 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_3 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_4 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_5 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_6 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_7 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_8 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_9 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_10 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_11 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_12 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_13 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_3_14 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_3_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)
    · rcases hs3 with s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3 | s3
      · exact n4l_tB_4_4_0 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_1 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_2 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_3 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_4 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_5 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_1_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_6 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_7 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_8 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_0_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_9 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_2_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_10 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_11 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_1_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_12 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_3_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_13 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_2_4_of_pos m.hlam ho3 s3 hp3)
      · exact n4l_tB_4_4_14 m (msig1_4_of_pos m.hlam ho0 s0 hp0) (msig1_4_of_pos m.hlam ho2 s2 hp2) (msig2_3_4_of_pos m.hlam ho3 s3 hp3)

theorem n4cert_pair04_em (m : N4Model)
    {x00 x01 x02 x03 : ℝ}
    (ho0 : m.t 0 ≤ x00 ∧ x00 ≤ x01 ∧ x01 ≤ x02 ∧ x02 ≤ x03 ∧ x03 ≤ m.t 0 + m.p)
    (hs0 : RowSig2 m.lam m.p (m.t 0) x00 x01 x02 x03)
    (hp0 : List.Perm [x00, x01, x02, x03] [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4)])
    {x40 x41 x42 x43 : ℝ}
    (ho4 : m.t 4 ≤ x40 ∧ x40 ≤ x41 ∧ x41 ≤ x42 ∧ x42 ≤ x43 ∧ x43 ≤ m.t 4 + m.p)
    (hs4 : RowSig2 m.lam m.p (m.t 4) x40 x41 x42 x43)
    (hp4 : List.Perm [x40, x41, x42, x43] [(m.d 0 4), (m.d 1 4), (m.d 2 4), (m.d 3 4)])
    (hem : (m.t 0 + m.p - m.lam < m.d 0 1) ∨ (m.t 0 + m.p - m.lam < m.d 0 2) ∨
      (m.t 0 + m.p - m.lam < m.d 0 3) ∨ (m.d 1 4 < m.t 4 + m.lam) ∨
      (m.d 2 4 < m.t 4 + m.lam) ∨ (m.d 3 4 < m.t 4 + m.lam))
    : False := by
  rcases hs0 with s0 | s0 | s0 | s0 | s0 | s0 | s0 | s0 | s0 | s0 | s0 | s0 | s0 | s0 | s0
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_0_0 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_1 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_2 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_3 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_4 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_5 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_6 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_7 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_8 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_9 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_10 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_11 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_12 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_13 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_0_14 m (msig2_0_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_1_0 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_1 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_2 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_3 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_4 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_5 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_6 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_7 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_8 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_9 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_10 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_11 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_12 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_13 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_1_14 m (msig2_1_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_2_0 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_1 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_2 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_3 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_4 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_5 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_6 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_7 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_8 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_9 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_10 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_11 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_12 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_13 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_2_14 m (msig2_2_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_3_0 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_1 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_2 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_3 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_4 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_5 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_6 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_7 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_8 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_9 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_10 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_11 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_12 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_13 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_3_14 m (msig2_3_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_4_0 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_1 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_2 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_3 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_4 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_5 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_6 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_7 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_8 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_9 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_10 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_11 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_12 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_13 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_4_14 m (msig2_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_5_0 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_1 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_2 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_3 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_4 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_5 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_6 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_7 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_8 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_9 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_10 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_11 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_12 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_13 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_5_14 m (msig2_0_1_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_6_0 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_1 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_2 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_3 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_4 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_5 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_6 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_7 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_8 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_9 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_10 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_11 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_12 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_13 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_6_14 m (msig2_0_2_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_7_0 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_1 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_2 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_3 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_4 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_5 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_6 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_7 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_8 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_9 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_10 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_11 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_12 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_13 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_7_14 m (msig2_0_3_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_8_0 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_1 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_2 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_3 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_4 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_5 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_6 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_7 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_8 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_9 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_10 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_11 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_12 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_13 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_8_14 m (msig2_0_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_9_0 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_1 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_2 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_3 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_4 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_5 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_6 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_7 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_8 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_9 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_10 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_11 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_12 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_13 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_9_14 m (msig2_1_2_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_10_0 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_1 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_2 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_3 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_4 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_5 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_6 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_7 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_8 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_9 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_10 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_11 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_12 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_13 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_10_14 m (msig2_1_3_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_11_0 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_1 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_2 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_3 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_4 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_5 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_6 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_7 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_8 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_9 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_10 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_11 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_12 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_13 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_11_14 m (msig2_1_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_12_0 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_1 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_2 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_3 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_4 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_5 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_6 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_7 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_8 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_9 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_10 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_11 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_12 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_13 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_12_14 m (msig2_2_3_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_13_0 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_1 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_2 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_3 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_4 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_5 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_6 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_7 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_8 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_9 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_10 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_11 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_12 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_13 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_13_14 m (msig2_2_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem
  · rcases hs4 with s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4 | s4
    · exact n4l_pE_14_0 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_1 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_2 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_3 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_4 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_5 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_1_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_6 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_7 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_8 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_0_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_9 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_2_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_10 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_11 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_1_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_12 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_3_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_13 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_2_4_of_pos m.hlam ho4 s4 hp4) hem
    · exact n4l_pE_14_14 m (msig2_3_4_of_pos m.hlam ho0 s0 hp0) (msig2_3_4_of_pos m.hlam ho4 s4 hp4) hem

end R2N4
