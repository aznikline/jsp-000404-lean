import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S7
import Jsp000404.R1LeavesN7_25S9
import Jsp000404.R1LeavesN7_25S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h4678 | h4678
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h5679 | h5679
  · rcases m.htr 0 3 5 (by decide) (by decide) with h5680 | h5680
    · linarith only [h4675, h4677, h5680, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5682 | h5682
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5683 | h5683
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5684 | h5684
          · linarith only [h4675, h4677, h5679, h5684, hc12, hlam, hphi, ht01, u0ehi3]
          · linarith only [h0, h5684, hc25, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h3871, h4676, h5682, h5683, hc02, hlam, hphi, u0ehi0]
      · linarith only [h4675, h4677, h5682, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h5689 | h5689
    · linarith only [h4675, h4677, h5689, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5691 | h5691
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5692 | h5692
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5693 | h5693
          · linarith only [h4677, h5693, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h5693, hc25, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h3871, h4676, h5691, h5692, hc02, hlam, hphi, u0ehi0]
      · linarith only [h4675, h4677, h5691, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h4677 | h4677
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h5698 | h5698
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5699 | h5699
    · linarith only [h4675, h4676, h5699, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5701 | h5701
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5702 | h5702
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5703 | h5703
          · linarith only [h3871, h4675, h4676, h5703, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h5703, hc24, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h5702, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5707 | h5707
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5708 | h5708
          · linarith only [h3871, h4676, h5698, h5701, h5708, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h5708, hc24, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h4675, h5707, hc02, hlam, hphi, u0ehi0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5712 | h5712
    · linarith only [h4675, h4676, h5712, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5714 | h5714
      · linarith only [h4675, h5698, h5714, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5716 | h5716
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5717 | h5717
          · linarith only [h4676, h5717, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h5717, hc24, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h4675, h5716, hc02, hlam, hphi, u0ehi0]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4676 | h4676
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5721 | h5721
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5722 | h5722
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5723 | h5723
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5724 | h5724
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5725 | h5725
          · linarith only [h4675, h5725, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h5725, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h4675, h5722, h5724, hlam]
      · linarith only [h4675, h5721, h5723, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5730 | h5730
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5731 | h5731
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5732 | h5732
          · linarith only [h4675, h5721, h5732, hc12, hlam, hphi, ht01, u0ehi3]
          · linarith only [h0, h5732, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5735 | h5735
          · linarith only [h4675, h5721, h5735, hc12, hlam, hphi, ht01, u0ehi3]
          · linarith only [h0, h5735, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h4675, h5721, h5730, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5739 | h5739
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5740 | h5740
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5741 | h5741
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5742 | h5742
          · linarith only [h0, h4675, h5742, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h5742, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h5721, h5739, h5740, h5741, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5746 | h5746
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5747 | h5747
          · linarith only [h0, h4675, h5747, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h5747, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h4675, h5739, h5746, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5751 | h5751
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5752 | h5752
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5753 | h5753
          · linarith only [h4675, h5753, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h5753, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5756 | h5756
          · linarith only [h0, h4675, h5756, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h5756, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5759 | h5759
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5760 | h5760
          · linarith only [h0, h4675, h5760, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h5760, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5763 | h5763
          · linarith only [h0, h4675, h5763, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h5763, hc23, hlam, hphi, ht01, ht12, u0ehi0]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4675 | h4675
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0 m hb0 hb2 hb3 h0 h3871 h4675
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x1 m hb0 hb2 hb3 h0 h3871 h4675

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h3871 | h3871
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x0 m hb0 hb2 hb3 h0 h3871
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1 m hb0 hb2 hb3 h0 h3871

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_23_L_R_L_I_H_I_x0 m hb0 hb2 hb3 h0
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1 m hb0 hb2 hb3 h0

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
  · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
      · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
          · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
              · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h10, h15, h18, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h10, h15, h17, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                · linarith only [h0, h10, h13, h17, h21, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h0bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h16, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h15, h17, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h1, hlam, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h4, hlam, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h15, h17, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h15, h17, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h2, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h5, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h7, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h15, h17, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h3, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h6, hlam, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h8, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h9, hlam, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
            · linarith only [h15, h16, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
            · linarith only [h0, h10, h13, h15, h50, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
              · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                · rcases h0bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, h10, h13, h15, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h1, h13, h15, h52, hc01, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h5, h52, hc01, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h50, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h1, h13, h15, h52, hc02, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, h5, h52, hc01, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, h50, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h1, hlam, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h4, hlam, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h5, h52, hc03, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, h4, h50, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h2, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h5, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h7, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h50, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h3, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h6, hlam, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h8, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h9, hlam, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                · linarith only [h0, h10, h13, h14, h15, h53, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                · linarith only [h0, h10, h13, h52, h81, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h15, h81, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
          · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
            · rcases m.htr 2 4 5 (by decide) (by decide) with h86 | h86
              · linarith only [h11, h14, h86, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                · linarith only [h11, h14, h84, h88, hlam]
                · rcases h0bigk with h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h4, h85, h88, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h14, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h14, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h0, hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h14, h7, h9, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h0, h14, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h0, h14, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h1, hlam, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h4, hlam, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h14, h9, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h0, h14, h4, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h2, hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h5, hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h7, hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h0, h14, h4, h7, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h3, hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h6, hlam, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h8, hlam, p90_0]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [h9, hlam, p90_1]
                  · have p90_0 := h90c.1
                    have p90_1 := h90c.2.1
                    have p90_2 := h90c.2.2.1
                    have p90_3 := h90c.2.2.2
                    linarith only [hlam, p90_0]
            · linarith only [h8, h84, h85, hc34, hlam, hphi, ht45, u5elo0]
          · linarith only [h13, h14, h84, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
        · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
          · linarith only [h0, h10, h119, h13, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h121 | h121
            · rcases m.htr 2 4 5 (by decide) (by decide) with h122 | h122
              · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                · rcases h0bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h1, h10, h121, h123, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h1, h10, h121, h123, hc01, hc45, hlam, hphi, ht0b, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h10, h121, h123, h13, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    rcases p124_3 (m.d 0 1) (by simp) with h129 | h129
                    · rcases p124_3 (m.d 0 2) (by simp) with h130 | h130
                      · linarith only [h0, h130, hlam]
                      · linarith only [h130, h6, hlam]
                    · linarith only [h129, h3, hlam]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h0, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h10, h121, h123, h13, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h0, h10, h121, h123, h13, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    rcases p124_3 (m.d 0 1) (by simp) with h138 | h138
                    · rcases p124_3 (m.d 0 2) (by simp) with h139 | h139
                      · rcases p124_3 (m.d 0 3) (by simp) with h140 | h140
                        · linarith only [h140, h4, hlam]
                        · linarith only [h140, h8, hlam]
                      · linarith only [h139, h6, hlam]
                    · linarith only [h138, h3, hlam]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h1, hlam, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h4, hlam, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h10, h121, h123, h13, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    rcases p124_3 (m.d 0 1) (by simp) with h149 | h149
                    · rcases p124_3 (m.d 0 2) (by simp) with h150 | h150
                      · rcases p124_3 (m.d 0 3) (by simp) with h151 | h151
                        · rcases p124_3 (m.d 0 4) (by simp) with h152 | h152
                          · linarith only [h152, h7, hlam]
                          · linarith only [h152, h9, hlam]
                        · linarith only [h151, h8, hlam]
                      · linarith only [h150, h6, hlam]
                    · linarith only [h149, h3, hlam]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h2, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h5, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h7, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    rcases p124_3 (m.d 0 1) (by simp) with h162 | h162
                    · rcases p124_3 (m.d 0 2) (by simp) with h163 | h163
                      · rcases p124_3 (m.d 0 3) (by simp) with h164 | h164
                        · rcases p124_3 (m.d 0 4) (by simp) with h165 | h165
                          · rcases p124_3 (m.d 0 5) (by simp) with h166 | h166
                            · linarith only [h166, h9, hlam]
                            · rcases h2bigk with h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h0, h10, h121, h123, hc01, hc45, hlam, hphi, ht0b, ht5b, p168_1]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                rcases p168_3 (m.d 0 2) (by simp) with h171 | h171
                                · rcases p168_3 (m.d 1 2) (by simp) with h172 | h172
                                  · linarith only [h0, h172, hlam]
                                  · linarith only [h10, h172, hlam]
                                · linarith only [h171, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                rcases p168_3 (m.d 0 2) (by simp) with h176 | h176
                                · rcases p168_3 (m.d 1 2) (by simp) with h177 | h177
                                  · linarith only [h0, h177, hlam]
                                  · linarith only [h11, h177, hlam]
                                · linarith only [h176, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h4, h6, h7, hlam, p124_1, p168_2]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h0, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h0, h121, h123, hc01, hc45, hlam, hphi, ht0b, ht5b, p168_1]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h0, h119, h121, h123, hc01, hc45, hlam, hphi, ht0b, ht5b, p168_1]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                rcases p168_3 (m.d 0 2) (by simp) with h186 | h186
                                · rcases p168_3 (m.d 1 2) (by simp) with h187 | h187
                                  · rcases p168_3 (m.d 2 3) (by simp) with h188 | h188
                                    · linarith only [h10, h188, hlam]
                                    · linarith only [h121, h188, hlam]
                                  · linarith only [h187, hlam, p168_0]
                                · linarith only [h186, h6, hlam]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h4, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h10, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h119, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h0, h10, h13, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p168_1]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h5, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h11, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p168_1]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h0, h11, h121, h123, hc01, hc45, hlam, hphi, ht0b, ht5b, p168_1]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h6, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h12, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h121, hlam, p168_1]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [h122, hlam, p168_0]
                              · have p168_0 := h168c.1
                                have p168_1 := h168c.2.1
                                have p168_2 := h168c.2.2.1
                                have p168_3 := h168c.2.2.2
                                linarith only [hlam, p168_0]
                          · linarith only [h165, h9, hlam]
                        · linarith only [h164, h8, hlam]
                      · linarith only [h163, h6, hlam]
                    · linarith only [h162, h3, hlam]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h3, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h6, hlam, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h8, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h9, hlam, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
                · linarith only [h10, h121, h123, h13, hc35, hlam, hphi, u5elo4]
              · linarith only [h118, h119, h121, h122, h3, hc35, hlam, hphi, u5elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h219 | h219
              · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                · rcases h0bigk with h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h13, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h13, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h219, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h121, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h0, hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h13, h7, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h0, h219, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h0, h121, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h1, hlam, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h4, hlam, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h219, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h0, h121, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h2, hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h5, hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h7, hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h121, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h3, hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h6, hlam, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h8, hlam, p221_0]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [h9, hlam, p221_1]
                  · have p221_0 := h221c.1
                    have p221_1 := h221c.2.1
                    have p221_2 := h221c.2.2.1
                    have p221_3 := h221c.2.2.2
                    linarith only [hlam, p221_0]
                · linarith only [h10, h13, h220, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                · rcases h0bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h13, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h13, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h119, h219, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h118, h119, h219, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h0, hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h119, h219, h248, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h0, h119, h219, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h0, h118, h119, h219, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h1, hlam, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h4, hlam, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h119, h219, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h0, h118, h119, h219, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h2, hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h5, hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h7, hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h118, h119, h219, h3, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h3, hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h6, hlam, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h8, hlam, p249_0]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [h9, hlam, p249_1]
                  · have p249_0 := h249c.1
                    have p249_1 := h249c.2.1
                    have p249_2 := h249c.2.2.1
                    have p249_3 := h249c.2.2.2
                    linarith only [hlam, p249_0]
                · linarith only [h118, h13, h248, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
          · linarith only [h10, h13, h276, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
            · linarith only [h10, h118, h13, h278, h9, hc35, hlam, hphi, u5elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
              · linarith only [h0, h10, h11, h118, h13, h280, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                · rcases h0bigk with h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h118, h282, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h118, h282, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h10, h118, h13, h282, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h0, hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h10, h118, h13, h282, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h0, h10, h118, h13, h282, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h0, h10, h118, h13, h282, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h1, hlam, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h4, hlam, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h10, h118, h13, h282, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h0, h10, h118, h13, h282, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h2, hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h5, hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h7, hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h10, h118, h13, h282, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h3, hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h6, hlam, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h8, hlam, p283_0]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [h9, hlam, p283_1]
                  · have p283_0 := h283c.1
                    have p283_1 := h283c.2.1
                    have p283_2 := h283c.2.2.1
                    have p283_3 := h283c.2.2.2
                    linarith only [hlam, p283_0]
                · linarith only [h10, h13, h282, hc23, hlam, hphi, ht34, ht45, u5elo4]
    · linarith only [h10, h12, h6, hc23, hlam, hphi, ht34, ht45, u5elo0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
    · rcases m.htr 1 3 4 (by decide) (by decide) with h312 | h312
      · linarith only [h10, h11, h312, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h314 | h314
        · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
          · linarith only [h10, h11, h312, h315, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h317 | h317
            · linarith only [h0, h10, h11, h315, h317, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h319 | h319
              · rcases m.htr 3 4 5 (by decide) (by decide) with h320 | h320
                · rcases h0bigk with h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h11, h315, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h11, h311, h315, h317, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h11, h2, h311, h317, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h317, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h0, hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h11, h311, h315, h317, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h0, h11, h311, h315, h317, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h0, h317, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h1, hlam, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h4, hlam, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h11, h311, h315, h317, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h0, h317, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h2, hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h5, hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h7, hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h317, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h3, hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h6, hlam, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h8, hlam, p321_0]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [h9, hlam, p321_1]
                  · have p321_0 := h321c.1
                    have p321_1 := h321c.2.1
                    have p321_2 := h321c.2.2.1
                    have p321_3 := h321c.2.2.2
                    linarith only [hlam, p321_0]
                · linarith only [h11, h311, h315, h319, h320, hlam]
              · linarith only [h11, h311, h317, h319, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h11, h311, h314, h9, hc25, hlam, hphi, u5elo0]
    · linarith only [h10, h311, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
