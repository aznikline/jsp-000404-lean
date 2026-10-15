import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3872 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3873 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3874 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h4632 | h4632
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4633 | h4633
    · linarith only [h0, h3871, h3874, h4633, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4635 | h4635
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4636 | h4636
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4637 | h4637
          · linarith only [h0, h3874, h4637, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h3871, h4632, h4637, hc25, hlam, hphi, ht01, ht12, u0ehi3]
        · linarith only [h0, h3871, h3873, h4632, h4636, hc02, hlam, hphi, u0ehi3]
      · linarith only [h0, h3871, h4632, h4635, hc23, hlam, hphi, ht01, ht12, u0ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4642 | h4642
    · linarith only [h0, h3871, h3874, h4642, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4644 | h4644
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4645 | h4645
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4646 | h4646
          · linarith only [h0, h3874, h4646, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h3871, h4646, hc25, hlam, hphi, ht01, ht12, u0ehi2]
        · linarith only [h0, h3871, h3873, h4645, hc02, hlam, hphi, u0ehi2]
      · linarith only [h0, h3871, h4644, hc23, hlam, hphi, ht01, ht12, u0ehi2]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3872 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3873 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h3874 | h3874
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h3872 h3873 h3874
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h3872 h3873 h3874

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3872 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3873 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h4651 | h4651
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4652 | h4652
    · linarith only [h0, h3871, h3873, h4652, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4654 | h4654
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4655 | h4655
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4656 | h4656
          · linarith only [h0, h3871, h3873, h4654, h4656, hc12, hlam, hphi, ht01, u0ehi4]
          · linarith only [h0, h3871, h4654, h4656, hc24, hlam, hphi, ht01, ht12, u0ehi4]
        · linarith only [h0, h3871, h4654, h4655, hc23, hlam, hphi, ht01, ht12, u0ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4660 | h4660
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4661 | h4661
          · linarith only [h0, h3873, h4661, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h3871, h4661, hc24, hlam, hphi, ht01, ht12, u0ehi2]
        · linarith only [h0, h3871, h4660, hc23, hlam, hphi, ht01, ht12, u0ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4665 | h4665
    · linarith only [h0, h3871, h3873, h4665, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4667 | h4667
      · linarith only [h0, h3871, h4651, h4667, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4669 | h4669
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4670 | h4670
          · linarith only [h0, h3871, h3873, h4670, hc12, hlam, hphi, ht01, u0ehi2]
          · linarith only [h0, h3871, h4670, hc24, hlam, hphi, ht01, ht12, u0ehi2]
        · linarith only [h0, h3871, h4669, hc23, hlam, hphi, ht01, ht12, u0ehi2]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3872 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h3873 | h3873
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h3872 h3873
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h3872 h3873

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3872 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  linarith only [h0, h3871, h3872, hlam]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h3872 | h3872
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x0 m hb0 hb2 hb3 h0 h3871 h3872
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x0_x1 m hb0 hb2 hb3 h0 h3871 h3872

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4682 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4683 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4684 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4685 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h4686 | h4686
  · rcases m.htr 2 4 5 (by decide) (by decide) with h4687 | h4687
    · rcases m.htr 3 4 5 (by decide) (by decide) with h4688 | h4688
      · rcases h2bigk with h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h0, hlam, p4689_1]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4685, h4688, hc02, hc45, hlam, hphi, ht0b, ht5b, p4689_1]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          rcases p4689_3 (m.d 0 2) (by simp) with h4693 | h4693
          · rcases p4689_3 (m.d 1 2) (by simp) with h4694 | h4694
            · rcases p4689_3 (m.d 2 3) (by simp) with h4695 | h4695
              · linarith only [h4675, h4695, hlam]
              · linarith only [h4685, h4695, hlam]
            · linarith only [h4681, h4694, hlam]
          · linarith only [h4693, hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          rcases p4689_3 (m.d 0 2) (by simp) with h4700 | h4700
          · rcases p4689_3 (m.d 1 2) (by simp) with h4701 | h4701
            · rcases p4689_3 (m.d 2 3) (by simp) with h4702 | h4702
              · linarith only [h4675, h4702, hlam]
              · linarith only [h4686, h4702, hlam]
            · linarith only [h4682, h4701, hlam]
          · linarith only [h4700, hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p4689_1, u0ehi1]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4685, h4688, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4689_1]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          rcases p4689_3 (m.d 0 2) (by simp) with h4710 | h4710
          · linarith only [h0, h4710, hlam]
          · linarith only [h4676, h4710, hlam]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          rcases p4689_3 (m.d 0 2) (by simp) with h4713 | h4713
          · linarith only [h0, h4713, hlam]
          · linarith only [h4677, h4713, hlam]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4675, hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4680, hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4675, h4685, h4688, hc02, hc45, hlam, hphi, ht0b, ht5b, p4689_1]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          rcases p4689_3 (m.d 0 2) (by simp) with h4720 | h4720
          · rcases p4689_3 (m.d 1 2) (by simp) with h4721 | h4721
            · rcases p4689_3 (m.d 2 3) (by simp) with h4722 | h4722
              · rcases p4689_3 (m.d 2 4) (by simp) with h4723 | h4723
                · linarith only [h4685, h4723, hlam]
                · linarith only [h4687, h4723, hlam]
              · linarith only [h4686, h4722, hlam]
            · linarith only [h4682, h4721, hlam]
          · linarith only [h4677, h4720, hlam]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4676, hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4681, hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4685, hlam, p4689_1]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          rcases p4689_3 (m.d 0 2) (by simp) with h4733 | h4733
          · rcases p4689_3 (m.d 1 2) (by simp) with h4734 | h4734
            · rcases p4689_3 (m.d 2 3) (by simp) with h4735 | h4735
              · rcases p4689_3 (m.d 2 4) (by simp) with h4736 | h4736
                · rcases p4689_3 (m.d 2 5) (by simp) with h4737 | h4737
                  · linarith only [h4687, h4737, hlam]
                  · rcases h3bigk with h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h3871, hlam, p4739_1]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4685, hc03, hc25, hlam, hphi, ht0b, ht5b, p4689_1, p4739_1]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4688, hc03, hc45, hlam, hphi, ht0b, ht5b, p4739_1]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      rcases p4739_3 (m.d 0 3) (by simp) with h4744 | h4744
                      · rcases p4739_3 (m.d 1 3) (by simp) with h4745 | h4745
                        · rcases p4739_3 (m.d 2 3) (by simp) with h4746 | h4746
                          · linarith only [h4675, h4746, hlam]
                          · linarith only [h4686, h4746, hlam]
                        · linarith only [h4684, h4745, hlam]
                      · linarith only [h4744, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p4739_1, u0ehi2]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4680, h4685, h4686, h4688, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4689_1, p4739_1]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4680, h4688, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4739_1]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      rcases p4739_3 (m.d 0 3) (by simp) with h4755 | h4755
                      · linarith only [h3871, h4755, hlam]
                      · linarith only [h4679, h4755, hlam]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4675, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4680, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4675, h4688, hc02, hc45, hlam, hphi, ht0b, ht5b, p4739_1]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h0, h4675, h4688, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4739_1]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4678, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4683, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4685, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4678, h4688, hc03, hc45, hlam, hphi, ht0b, ht5b, p4739_1]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4679, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4684, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4686, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [h4688, hlam, p4739_0]
                    · have p4739_0 := h4739c.1
                      have p4739_1 := h4739c.2.1
                      have p4739_2 := h4739c.2.2.1
                      have p4739_3 := h4739c.2.2.2
                      linarith only [hlam, p4739_0]
                · linarith only [h4687, h4736, hlam]
              · linarith only [h4686, h4735, hlam]
            · linarith only [h4682, h4734, hlam]
          · linarith only [h4677, h4733, hlam]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4677, hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4682, hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4686, hlam, p4689_1]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [h4687, hlam, p4689_0]
        · have p4689_0 := h4689c.1
          have p4689_1 := h4689c.2.1
          have p4689_2 := h4689c.2.2.1
          have p4689_3 := h4689c.2.2.2
          linarith only [hlam, p4689_0]
      · rcases h2bigk with h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c | h4782c
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h0, hlam, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h0, h4685, h4687, h4688, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h0, h4687, h4688, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          rcases p4782_3 (m.d 0 2) (by simp) with h4787 | h4787
          · rcases p4782_3 (m.d 1 2) (by simp) with h4788 | h4788
            · rcases p4782_3 (m.d 2 3) (by simp) with h4789 | h4789
              · linarith only [h4675, h4789, hlam]
              · linarith only [h4686, h4789, hlam]
            · linarith only [h4682, h4788, hlam]
          · linarith only [h4787, hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p4782_1, u0ehi1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4685, h4687, h4688, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4687, h4688, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          rcases p4782_3 (m.d 0 2) (by simp) with h4798 | h4798
          · linarith only [h0, h4798, hlam]
          · linarith only [h4677, h4798, hlam]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4675, hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4680, hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4675, h4687, h4688, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h0, h4675, h4687, h4688, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4676, hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4681, hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4685, hlam, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h0, h4676, h4687, h4688, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4677, hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4682, hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4686, hlam, p4782_1]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [h4687, hlam, p4782_0]
        · have p4782_0 := h4782c.1
          have p4782_1 := h4782c.2.1
          have p4782_2 := h4782c.2.2.1
          have p4782_3 := h4782c.2.2.2
          linarith only [hlam, p4782_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h4816 | h4816
      · linarith only [h4675, h4685, h4687, h4816, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases h2bigk with h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c | h4818c
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h0, hlam, p4818_1]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          rcases p4818_3 (m.d 0 2) (by simp) with h4821 | h4821
          · rcases p4818_3 (m.d 1 2) (by simp) with h4822 | h4822
            · rcases p4818_3 (m.d 2 3) (by simp) with h4823 | h4823
              · linarith only [h4823, hlam, p4818_0]
              · rcases p4818_3 (m.d 2 4) (by simp) with h4825 | h4825
                · linarith only [h4676, h4825, hlam]
                · rcases p4818_3 (m.d 2 5) (by simp) with h4827 | h4827
                  · linarith only [h4677, h4827, hlam]
                  · rcases h3bigk with h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c | h4829c
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h3871, hlam, p4829_1]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4675, hlam, p4818_2, p4829_1]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      rcases p4829_3 (m.d 0 3) (by simp) with h4833 | h4833
                      · rcases p4829_3 (m.d 1 3) (by simp) with h4834 | h4834
                        · rcases p4829_3 (m.d 2 3) (by simp) with h4835 | h4835
                          · linarith only [h4675, h4835, hlam]
                          · linarith only [h4685, h4835, hlam]
                        · linarith only [h4683, h4834, hlam]
                      · linarith only [h4833, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      rcases p4829_3 (m.d 0 3) (by simp) with h4840 | h4840
                      · rcases p4829_3 (m.d 1 3) (by simp) with h4841 | h4841
                        · rcases p4829_3 (m.d 2 3) (by simp) with h4842 | h4842
                          · linarith only [h4675, h4842, hlam]
                          · linarith only [h4686, h4842, hlam]
                        · linarith only [h4684, h4841, hlam]
                      · linarith only [h4840, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [hc13, hlam, hphi, ht01, p4829_1, u0ehi2]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4680, h4686, h4816, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4829_1]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      rcases p4829_3 (m.d 0 3) (by simp) with h4850 | h4850
                      · linarith only [h3871, h4850, hlam]
                      · linarith only [h4678, h4850, hlam]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      rcases p4829_3 (m.d 0 3) (by simp) with h4853 | h4853
                      · linarith only [h3871, h4853, hlam]
                      · linarith only [h4679, h4853, hlam]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4675, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4680, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4818_1, p4829_1]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h0, h4816, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4818_1, p4829_1]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4678, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4683, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4685, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4816, hlam, p4829_1]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4679, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4684, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4686, hlam, p4829_0]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [h4679, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4829_1]
                    · have p4829_0 := h4829c.1
                      have p4829_1 := h4829c.2.1
                      have p4829_2 := h4829c.2.2.1
                      have p4829_3 := h4829c.2.2.2
                      linarith only [hlam, p4829_0]
            · linarith only [h4680, h4822, hlam]
          · linarith only [h4821, hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          rcases p4818_3 (m.d 0 2) (by simp) with h4873 | h4873
          · rcases p4818_3 (m.d 1 2) (by simp) with h4874 | h4874
            · rcases p4818_3 (m.d 2 3) (by simp) with h4875 | h4875
              · linarith only [h4675, h4875, hlam]
              · linarith only [h4685, h4875, hlam]
            · linarith only [h4681, h4874, hlam]
          · linarith only [h4873, hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          rcases p4818_3 (m.d 0 2) (by simp) with h4880 | h4880
          · rcases p4818_3 (m.d 1 2) (by simp) with h4881 | h4881
            · rcases p4818_3 (m.d 2 3) (by simp) with h4882 | h4882
              · linarith only [h4675, h4882, hlam]
              · linarith only [h4686, h4882, hlam]
            · linarith only [h4682, h4881, hlam]
          · linarith only [h4880, hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p4818_1, u0ehi1]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          rcases p4818_3 (m.d 0 2) (by simp) with h4889 | h4889
          · linarith only [h0, h4889, hlam]
          · linarith only [h4675, h4889, hlam]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          rcases p4818_3 (m.d 0 2) (by simp) with h4892 | h4892
          · linarith only [h0, h4892, hlam]
          · linarith only [h4676, h4892, hlam]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          rcases p4818_3 (m.d 0 2) (by simp) with h4895 | h4895
          · linarith only [h0, h4895, hlam]
          · linarith only [h4677, h4895, hlam]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h4675, hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h4680, hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          rcases p4818_3 (m.d 0 2) (by simp) with h4901 | h4901
          · rcases p4818_3 (m.d 1 2) (by simp) with h4902 | h4902
            · rcases p4818_3 (m.d 2 3) (by simp) with h4903 | h4903
              · rcases p4818_3 (m.d 2 4) (by simp) with h4904 | h4904
                · linarith only [h4685, h4904, hlam]
                · rcases p4818_3 (m.d 2 5) (by simp) with h4906 | h4906
                  · linarith only [h4686, h4906, hlam]
                  · linarith only [h4687, h4906, hlam]
              · linarith only [h4685, h4903, hlam]
            · linarith only [h4681, h4902, hlam]
          · linarith only [h4676, h4901, hlam]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          rcases p4818_3 (m.d 0 2) (by simp) with h4912 | h4912
          · rcases p4818_3 (m.d 1 2) (by simp) with h4913 | h4913
            · rcases p4818_3 (m.d 2 3) (by simp) with h4914 | h4914
              · rcases p4818_3 (m.d 2 4) (by simp) with h4915 | h4915
                · linarith only [h4685, h4915, hlam]
                · rcases p4818_3 (m.d 2 5) (by simp) with h4917 | h4917
                  · linarith only [h4686, h4917, hlam]
                  · rcases h3bigk with h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h3871, hlam, p4919_1]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4685, h4687, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4818_1, p4919_1]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      rcases p4919_3 (m.d 0 3) (by simp) with h4923 | h4923
                      · rcases p4919_3 (m.d 1 3) (by simp) with h4924 | h4924
                        · rcases p4919_3 (m.d 2 3) (by simp) with h4925 | h4925
                          · linarith only [h4675, h4925, hlam]
                          · linarith only [h4685, h4925, hlam]
                        · linarith only [h4683, h4924, hlam]
                      · linarith only [h4923, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      rcases p4919_3 (m.d 0 3) (by simp) with h4930 | h4930
                      · rcases p4919_3 (m.d 1 3) (by simp) with h4931 | h4931
                        · rcases p4919_3 (m.d 2 3) (by simp) with h4932 | h4932
                          · linarith only [h4675, h4932, hlam]
                          · linarith only [h4686, h4932, hlam]
                        · linarith only [h4684, h4931, hlam]
                      · linarith only [h4930, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p4919_1, u0ehi2]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4680, h4685, h4687, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4818_1, p4919_1]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      rcases p4919_3 (m.d 0 3) (by simp) with h4940 | h4940
                      · linarith only [h3871, h4940, hlam]
                      · linarith only [h4678, h4940, hlam]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      rcases p4919_3 (m.d 0 3) (by simp) with h4943 | h4943
                      · linarith only [h3871, h4943, hlam]
                      · linarith only [h4679, h4943, hlam]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4675, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4680, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h0, h4675, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4919_1]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h0, h4675, h4816, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4919_1]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4678, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4683, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4685, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4816, hlam, p4919_1]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4679, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4684, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4686, hlam, p4919_0]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [h4679, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4919_1]
                    · have p4919_0 := h4919c.1
                      have p4919_1 := h4919c.2.1
                      have p4919_2 := h4919c.2.2.1
                      have p4919_3 := h4919c.2.2.2
                      linarith only [hlam, p4919_0]
              · linarith only [h4686, h4914, hlam]
            · linarith only [h4682, h4913, hlam]
          · linarith only [h4677, h4912, hlam]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h4676, hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h4681, hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h4685, hlam, p4818_1]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h4687, hlam, p4818_1]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h4677, hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h4682, hlam, p4818_0]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [h4686, hlam, p4818_1]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          rcases p4818_3 (m.d 0 2) (by simp) with h4972 | h4972
          · rcases p4818_3 (m.d 1 2) (by simp) with h4973 | h4973
            · rcases p4818_3 (m.d 2 3) (by simp) with h4974 | h4974
              · rcases p4818_3 (m.d 2 4) (by simp) with h4975 | h4975
                · linarith only [h4687, h4975, hlam]
                · rcases p4818_3 (m.d 2 5) (by simp) with h4977 | h4977
                  · rcases h3bigk with h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c | h4978c
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h3871, hlam, p4978_1]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h3871, h4680, h4686, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4978_1]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      rcases p4978_3 (m.d 0 3) (by simp) with h4982 | h4982
                      · rcases p4978_3 (m.d 1 3) (by simp) with h4983 | h4983
                        · rcases p4978_3 (m.d 2 3) (by simp) with h4984 | h4984
                          · linarith only [h4675, h4984, hlam]
                          · linarith only [h4685, h4984, hlam]
                        · linarith only [h4683, h4983, hlam]
                      · linarith only [h4982, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      rcases p4978_3 (m.d 0 3) (by simp) with h4989 | h4989
                      · rcases p4978_3 (m.d 1 3) (by simp) with h4990 | h4990
                        · rcases p4978_3 (m.d 2 3) (by simp) with h4991 | h4991
                          · linarith only [h4675, h4991, hlam]
                          · linarith only [h4686, h4991, hlam]
                        · linarith only [h4684, h4990, hlam]
                      · linarith only [h4989, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p4978_1, u0ehi2]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4680, h4685, h4686, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4818_1, p4978_1]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      rcases p4978_3 (m.d 0 3) (by simp) with h4999 | h4999
                      · linarith only [h3871, h4999, hlam]
                      · linarith only [h4678, h4999, hlam]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      rcases p4978_3 (m.d 0 3) (by simp) with h5002 | h5002
                      · linarith only [h3871, h5002, hlam]
                      · linarith only [h4679, h5002, hlam]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4675, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4680, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h0, h4675, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4978_1]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h0, h4675, h4816, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4978_1]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4678, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4683, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4685, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4816, hlam, p4978_1]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4679, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4684, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4686, hlam, p4978_0]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [h4679, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4978_1]
                    · have p4978_0 := h4978c.1
                      have p4978_1 := h4978c.2.1
                      have p4978_2 := h4978c.2.2.1
                      have p4978_3 := h4978c.2.2.2
                      linarith only [hlam, p4978_0]
                  · linarith only [h4687, h4977, hlam]
              · linarith only [h4685, h4974, hlam]
            · linarith only [h4681, h4973, hlam]
          · linarith only [h4676, h4972, hlam]
        · have p4818_0 := h4818c.1
          have p4818_1 := h4818c.2.1
          have p4818_2 := h4818c.2.2.1
          have p4818_3 := h4818c.2.2.2
          linarith only [hlam, p4818_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h5025 | h5025
    · linarith only [h4685, h4686, h5025, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h5027 | h5027
      · linarith only [h0, h4675, h4685, h5025, h5027, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h2bigk with h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c | h5029c
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h0, hlam, p5029_1]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          rcases p5029_3 (m.d 0 2) (by simp) with h5032 | h5032
          · rcases p5029_3 (m.d 1 2) (by simp) with h5033 | h5033
            · rcases p5029_3 (m.d 2 3) (by simp) with h5034 | h5034
              · linarith only [h5034, hlam, p5029_0]
              · rcases p5029_3 (m.d 2 4) (by simp) with h5036 | h5036
                · linarith only [h4676, h5036, hlam]
                · rcases p5029_3 (m.d 2 5) (by simp) with h5038 | h5038
                  · linarith only [h4677, h5038, hlam]
                  · linarith only [h4686, h5038, hlam]
            · linarith only [h4680, h5033, hlam]
          · linarith only [h5032, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          rcases p5029_3 (m.d 0 2) (by simp) with h5043 | h5043
          · rcases p5029_3 (m.d 1 2) (by simp) with h5044 | h5044
            · rcases p5029_3 (m.d 2 3) (by simp) with h5045 | h5045
              · linarith only [h4675, h5045, hlam]
              · linarith only [h4685, h5045, hlam]
            · linarith only [h4681, h5044, hlam]
          · linarith only [h5043, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          rcases p5029_3 (m.d 0 2) (by simp) with h5050 | h5050
          · rcases p5029_3 (m.d 1 2) (by simp) with h5051 | h5051
            · rcases p5029_3 (m.d 2 3) (by simp) with h5052 | h5052
              · linarith only [h4675, h5052, hlam]
              · rcases p5029_3 (m.d 2 4) (by simp) with h5054 | h5054
                · linarith only [h4676, h5054, hlam]
                · rcases p5029_3 (m.d 2 5) (by simp) with h5056 | h5056
                  · linarith only [h5056, hlam, p5029_0]
                  · rcases h3bigk with h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c | h5058c
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h3871, hlam, p5058_1]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h3871, h4680, h4685, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5058_1]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      rcases p5058_3 (m.d 0 3) (by simp) with h5062 | h5062
                      · rcases p5058_3 (m.d 1 3) (by simp) with h5063 | h5063
                        · rcases p5058_3 (m.d 2 3) (by simp) with h5064 | h5064
                          · linarith only [h4675, h5064, hlam]
                          · linarith only [h4685, h5064, hlam]
                        · linarith only [h4683, h5063, hlam]
                      · linarith only [h5062, hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h3871, h4680, h4685, h4686, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5058_1]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p5058_1, u0ehi2]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4680, h4685, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5058_1]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      rcases p5058_3 (m.d 0 3) (by simp) with h5073 | h5073
                      · linarith only [h3871, h5073, hlam]
                      · linarith only [h4678, h5073, hlam]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4680, h4685, h4686, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5058_1]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4675, hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4680, hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4675, h4679, h4686, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5058_1]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4686, hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4678, hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4683, hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4685, hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h5027, hlam, p5058_1]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4679, hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4684, hlam, p5058_0]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h4675, h4679, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5058_1]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [h0, h4675, h4679, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5058_1]
                    · have p5058_0 := h5058c.1
                      have p5058_1 := h5058c.2.1
                      have p5058_2 := h5058c.2.2.1
                      have p5058_3 := h5058c.2.2.2
                      linarith only [hlam, p5058_0]
            · linarith only [h4682, h5051, hlam]
          · linarith only [h5050, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p5029_1, u0ehi1]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          rcases p5029_3 (m.d 0 2) (by simp) with h5096 | h5096
          · linarith only [h0, h5096, hlam]
          · linarith only [h4675, h5096, hlam]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          rcases p5029_3 (m.d 0 2) (by simp) with h5099 | h5099
          · linarith only [h0, h5099, hlam]
          · linarith only [h4676, h5099, hlam]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          rcases p5029_3 (m.d 0 2) (by simp) with h5102 | h5102
          · linarith only [h0, h5102, hlam]
          · linarith only [h4677, h5102, hlam]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h4675, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h4680, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h4675, h4679, h4686, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p5029_1]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h4686, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h4676, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h4681, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h4685, hlam, p5029_1]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h5025, hlam, p5029_1]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h4677, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h4682, hlam, p5029_0]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [h0, h4677, h4685, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5029_1]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          rcases p5029_3 (m.d 0 2) (by simp) with h5118 | h5118
          · rcases p5029_3 (m.d 1 2) (by simp) with h5119 | h5119
            · rcases p5029_3 (m.d 2 3) (by simp) with h5120 | h5120
              · linarith only [h4686, h5120, hlam]
              · linarith only [h4685, h5120, hlam]
            · linarith only [h4681, h5119, hlam]
          · linarith only [h4676, h5118, hlam]
        · have p5029_0 := h5029c.1
          have p5029_1 := h5029c.2.1
          have p5029_2 := h5029c.2.2.1
          have p5029_3 := h5029c.2.2.2
          linarith only [hlam, p5029_0]

end R2N4
