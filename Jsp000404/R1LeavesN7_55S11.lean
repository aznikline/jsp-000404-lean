import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S8
import Jsp000404.R1LeavesN7_55S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1 m hb0 hb1 hb3 hb4 h0

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
          · rcases h1bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h0, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h7, h9, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u4ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p10_1]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h1, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h4, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h9, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u4ehi4]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h0, h4, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p10_1]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h2, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h5, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h7, hlam, p10_1]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h2, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p10_1]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h3, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h6, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h8, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [h9, hlam, p10_0]
            · have p10_0 := h10c.1
              have p10_1 := h10c.2.1
              have p10_2 := h10c.2.2.1
              have p10_3 := h10c.2.2.2
              linarith only [hlam, p10_0]
          · rcases h1bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p36_1, u4ehi3]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p36_1, u4ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p36_1, u4ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h0, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h7, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1, u4ehi3]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p36_1, u4ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h0, h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p36_1, u4ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h1, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h4, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h5, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1, u4ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h0, h4, h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p36_1, u4ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h2, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h5, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h7, hlam, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h9, hlam, p36_1]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h3, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h6, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h8, hlam, p36_0]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [h5, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1, u4ehi2]
            · have p36_0 := h36c.1
              have p36_1 := h36c.2.1
              have p36_2 := h36c.2.2.1
              have p36_3 := h36c.2.2.2
              linarith only [hlam, p36_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
          · linarith only [h62, h7, h8, hlam]
          · rcases h1bigk with h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p64_1]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p64_1, u4ehi3]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p64_1, u4ehi1]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p64_1, u4ehi3]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h0, hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h7, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p64_1, u4ehi3]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p64_1, u4ehi1]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h0, h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p64_1, u4ehi3]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h1, hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h4, hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h5, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p64_1, u4ehi2]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h8, hlam, p64_1]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h2, hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h5, hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h7, hlam, p64_1]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h62, hlam, p64_1]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h3, hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h6, hlam, p64_0]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p64_1]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [h0, h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p64_1, u4ehi2]
            · have p64_0 := h64c.1
              have p64_1 := h64c.2.1
              have p64_2 := h64c.2.2.1
              have p64_3 := h64c.2.2.2
              linarith only [hlam, p64_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
        · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
          · rcases h1bigk with h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p92_1]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h90, hc01, hc35, hlam, hphi, ht0b, ht5b, p92_1]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h91, hc01, hlam, hphi, ht0b, ht45, ht5b, p92_1, u4ehi4]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h91, hc01, hlam, hphi, ht0b, ht45, ht5b, p92_1, u4ehi4]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h0, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h90, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p92_1]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h0, h91, hc01, hlam, hphi, ht0b, ht45, ht5b, p92_1, u4ehi4]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p92_1]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h1, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h4, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h7, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h1, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p92_1]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h2, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h5, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p92_1]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h0, h5, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p92_1]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h3, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h6, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h90, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [h91, hlam, p92_0]
            · have p92_0 := h92c.1
              have p92_1 := h92c.2.1
              have p92_2 := h92c.2.2.1
              have p92_3 := h92c.2.2.2
              linarith only [hlam, p92_0]
          · linarith only [h7, h90, h91, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
          · rcases h1bigk with h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              rcases p120_3 (m.d 0 1) (by simp) with h123 | h123
              · rcases p120_3 (m.d 1 2) (by simp) with h124 | h124
                · linarith only [h0, h124, hlam]
                · linarith only [h124, h4, hlam]
              · linarith only [h123, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h119, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi4]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h119, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi4]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h0, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h0, h119, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi4]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h0, h119, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi4]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h1, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h4, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h7, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h90, hlam, p120_1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h2, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h5, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h0, h119, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi4]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h3, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h6, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h119, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
          · rcases h1bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              rcases p150_3 (m.d 0 1) (by simp) with h153 | h153
              · rcases p150_3 (m.d 1 2) (by simp) with h154 | h154
                · linarith only [h0, h154, hlam]
                · linarith only [h154, h4, hlam]
              · linarith only [h153, hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p150_1, u4ehi1]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h119, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p150_1, u4ehi2]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h0, hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p150_1, u4ehi2]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p150_1]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h1, hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h4, hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h7, hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h90, hlam, p150_1]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h2, hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h5, hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h119, hlam, p150_1]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h3, hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h6, hlam, p150_0]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p150_1, u4ehi1]
            · have p150_0 := h150c.1
              have p150_1 := h150c.2.1
              have p150_2 := h150c.2.2.1
              have p150_3 := h150c.2.2.2
              linarith only [hlam, p150_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
      · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
        · linarith only [h181, h4, h6, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
          · linarith only [h180, h183, h4, h6, hlam]
          · rcases h1bigk with h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h180, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p185_1, u4ehi1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h180, hc01, hlam, hphi, ht0b, ht45, ht5b, p185_1, u4ehi1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p185_1, u4ehi1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h180, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p185_1, u4ehi1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h0, hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h180, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p185_1, u4ehi1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p185_1, u4ehi1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h6, hlam, p185_1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h1, hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h4, hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p185_1, u4ehi1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h181, hlam, p185_1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h2, hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h5, hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h180, hlam, p185_1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h183, hlam, p185_1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h3, hlam, p185_0]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p185_1]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h180, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p185_1, u4ehi3]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p185_1, u4ehi2]
            · have p185_0 := h185c.1
              have p185_1 := h185c.2.1
              have p185_2 := h185c.2.2.1
              have p185_3 := h185c.2.2.2
              linarith only [hlam, p185_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h211 | h211
        · linarith only [h180, h211, h5, h6, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h213 | h213
          · linarith only [h213, h5, h6, hlam]
          · rcases h1bigk with h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p215_1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              rcases p215_3 (m.d 0 1) (by simp) with h218 | h218
              · rcases p215_3 (m.d 1 2) (by simp) with h219 | h219
                · linarith only [h0, h219, hlam]
                · linarith only [h219, h4, hlam]
              · linarith only [h218, hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p215_1, u4ehi1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p215_1, u4ehi2]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h0, hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h211, h6, hc13, hc35, hlam, hphi, p215_1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p215_1, u4ehi1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h6, hlam, p215_1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h1, hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h4, hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h180, hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h211, hlam, p215_1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h2, hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h5, hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h180, h4, hc23, hc34, hlam, hphi, p215_1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h213, hlam, p215_1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h3, hlam, p215_0]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p215_1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p215_1]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p215_1, u4ehi2]
            · have p215_0 := h215c.1
              have p215_1 := h215c.2.1
              have p215_2 := h215c.2.2.1
              have p215_3 := h215c.2.2.2
              linarith only [hlam, p215_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
    · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
      · linarith only [h246, h4, h5, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h248 | h248
        · rcases m.htr 1 4 5 (by decide) (by decide) with h249 | h249
          · rcases h1bigk with h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h245, hc01, hc25, hlam, hphi, ht0b, ht5b, p250_1]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h248, hc01, hc35, hlam, hphi, ht0b, ht5b, p250_1]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h249, hc01, hlam, hphi, ht0b, ht45, ht5b, p250_1, u4ehi4]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h249, hc01, hlam, hphi, ht0b, ht45, ht5b, p250_1, u4ehi4]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h0, hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h248, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p250_1]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h5, hlam, p250_1]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p250_1]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h1, hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h4, hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h246, hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h1, h245, hc01, hc25, hlam, hphi, ht0b, ht5b, p250_1]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h2, hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p250_1]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h2, h245, hc01, hc25, hlam, hphi, ht0b, ht5b, p250_1]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h3, hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h245, hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h248, hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [h249, hlam, p250_0]
            · have p250_0 := h250c.1
              have p250_1 := h250c.2.1
              have p250_2 := h250c.2.2.1
              have p250_3 := h250c.2.2.2
              linarith only [hlam, p250_0]
          · linarith only [h245, h249, h5, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
          · rcases h1bigk with h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p278_1]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              rcases p278_3 (m.d 0 1) (by simp) with h281 | h281
              · rcases p278_3 (m.d 1 2) (by simp) with h282 | h282
                · linarith only [h0, h282, hlam]
                · linarith only [h282, h4, hlam]
              · linarith only [h281, hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h277, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi4]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h277, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi4]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h0, hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p278_1]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h5, hlam, p278_1]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h277, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p278_1, u4ehi4]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h1, hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h4, hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h246, hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h248, hlam, p278_1]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h2, hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h246, hc12, hc34, hlam, hphi, ht23, p278_1]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p278_1]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h2, h277, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi4]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h3, hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h245, hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h0, h245, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p278_1]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [h277, hlam, p278_0]
            · have p278_0 := h278c.1
              have p278_1 := h278c.2.1
              have p278_2 := h278c.2.2.1
              have p278_3 := h278c.2.2.2
              linarith only [hlam, p278_0]
          · linarith only [h245, h277, h5, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h309 | h309
      · linarith only [h309, h4, h5, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h311 | h311
        · linarith only [h245, h311, h4, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h313 | h313
          · rcases h1bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              rcases p314_3 (m.d 0 1) (by simp) with h317 | h317
              · rcases p314_3 (m.d 1 2) (by simp) with h318 | h318
                · linarith only [h0, h318, hlam]
                · linarith only [h318, h4, hlam]
              · linarith only [h317, hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h313, hc01, hlam, hphi, ht0b, ht45, ht5b, p314_1, u4ehi4]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h245, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h0, hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h245, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h5, hlam, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h245, hlam, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h1, hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h4, hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h309, hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h311, hlam, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h2, hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h309, hc12, hc34, hlam, hphi, ht23, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h2, h245, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h3, hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p314_1]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [h313, hlam, p314_0]
            · have p314_0 := h314c.1
              have p314_1 := h314c.2.1
              have p314_2 := h314c.2.2.1
              have p314_3 := h314c.2.2.2
              linarith only [hlam, p314_0]
          · rcases h1bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              rcases p344_3 (m.d 0 1) (by simp) with h347 | h347
              · rcases p344_3 (m.d 1 2) (by simp) with h348 | h348
                · linarith only [h0, h348, hlam]
                · linarith only [h348, h4, hlam]
              · linarith only [h347, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p344_1, u4ehi1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h245, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h0, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h5, hlam, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h245, hlam, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h1, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h4, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h309, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h311, hlam, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h2, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h313, hlam, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h3, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p344_1, u4ehi1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]

end R2N4
