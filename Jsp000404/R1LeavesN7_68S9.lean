import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_68S7
import Jsp000404.R1LeavesN7_68S8

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_24_L_R_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_24_L_R_H_I_x0 m hb2 hb4 h0
  · exact r1l7_12_24_L_R_H_I_x1 m hb2 hb4 h0

theorem r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
      · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
            · rcases h0bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p13_1]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p13_1]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h12, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p13_1]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h0, hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h1, h11, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p13_1]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h0, h12, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h1, hlam, p13_1]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h4, hlam, p13_1]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h12, h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h2, hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h5, hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h6, hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h3, hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi1]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h7, hlam, p13_0]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [h8, hlam, p13_1]
              · have p13_0 := h13c.1
                have p13_1 := h13c.2.1
                have p13_2 := h13c.2.2.1
                have p13_3 := h13c.2.2.2
                linarith only [hlam, p13_0]
            · rcases h0bigk with h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h12, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h12, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h12, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h12, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h0, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h12, h6, h8, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h0, h12, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h0, h12, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h1, hlam, p39_1]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h4, hlam, p39_1]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h12, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h0, h12, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h2, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h5, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h6, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h12, h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h3, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h0, h11, h9, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p39_1, u1ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h7, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h8, hlam, p39_1]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
            · rcases h0bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h11, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h11, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h11, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi4]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h0, hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h11, h6, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi4]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h1, hlam, p66_1]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h4, hlam, p66_1]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h11, h6, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi4]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h2, hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h5, hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h6, hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi4]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h3, hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p66_1, u1ehi1]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h7, hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h8, hlam, p66_1]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
            · rcases h0bigk with h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [hlam, p92_0]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h11, h4, h6, h65, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h11, h6, h65, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h11, h65, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h11, h3, h65, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
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
                linarith only [h11, h6, h65, h8, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h0, h11, h65, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h0, h11, h65, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h1, hlam, p92_1]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h4, hlam, p92_1]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [hlam, p92_0]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h11, h65, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h0, h11, h4, h65, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
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
                linarith only [h6, hlam, p92_0]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [hlam, p92_0]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h11, h65, h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h3, hlam, p92_0]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h0, h10, h11, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p92_1, u1ehi2]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h7, hlam, p92_0]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [h8, hlam, p92_1]
              · have p92_0 := h92c.1
                have p92_1 := h92c.2.1
                have p92_2 := h92c.2.2.1
                have p92_3 := h92c.2.2.2
                linarith only [hlam, p92_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
          · linarith only [h10, h118, h9, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
            · rcases h0bigk with h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h10, h5, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi2]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h118, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi2]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h10, h5, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi2]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi4]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h0, hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h118, h6, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi2]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h0, h10, h5, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi2]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi4]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h1, hlam, p121_1]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h4, hlam, p121_1]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h10, h5, h9, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi2]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi4]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h2, hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h5, hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h6, hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi4]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h3, hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h0, h9, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p121_1, u1ehi2]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h7, hlam, p121_0]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [h8, hlam, p121_1]
              · have p121_0 := h121c.1
                have p121_1 := h121c.2.1
                have p121_2 := h121c.2.2.1
                have p121_3 := h121c.2.2.2
                linarith only [hlam, p121_0]
            · rcases h0bigk with h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h4, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h10, h120, h3, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p147_1, u1ehi2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h0, hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p147_1, u1ehi2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h0, h10, h2, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p147_1, u1ehi2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h0, h10, h120, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p147_1, u1ehi2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h1, hlam, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h4, hlam, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h10, h120, h8, h9, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p147_1, u1ehi2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h0, h10, h120, h4, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p147_1, u1ehi2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h2, hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h5, hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h6, hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h10, h120, h8, h9, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p147_1, u1ehi2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h3, hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h0, h9, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p147_1, u1ehi2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h7, hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h8, hlam, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
        · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
          · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
            · rcases h0bigk with h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h173, h175, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h173, h175, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h3, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h0, hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h173, h175, h4, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h0, h3, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h1, hlam, p176_1]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h4, hlam, p176_1]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h3, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h2, hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h5, hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h6, hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h3, hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h0, h173, h175, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p176_1, u1ehi4]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h7, hlam, p176_0]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [h8, hlam, p176_1]
              · have p176_0 := h176c.1
                have p176_1 := h176c.2.1
                have p176_2 := h176c.2.2.1
                have p176_3 := h176c.2.2.2
                linarith only [hlam, p176_0]
            · rcases h0bigk with h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h175, h4, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h175, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h175, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h175, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h0, hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h175, h6, h8, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h0, h175, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h0, h175, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h1, hlam, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h4, hlam, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h175, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h0, h175, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h2, hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h5, hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h6, hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h175, h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h3, hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h0, h173, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u1ehi3]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h7, hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h8, hlam, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hlam, p202_0]
          · linarith only [h173, h174, h9, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
          · rcases m.htr 1 4 5 (by decide) (by decide) with h230 | h230
            · rcases h0bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h4, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p231_1]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h1, h229, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi3]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi3]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi4]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h0, hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h1, h229, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi3]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi3]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi4]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h1, hlam, p231_1]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h4, hlam, p231_1]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h173, h5, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi1]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi4]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h2, hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h5, hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h6, hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi4]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h3, hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi1]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h7, hlam, p231_0]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [h8, hlam, p231_1]
              · have p231_0 := h231c.1
                have p231_1 := h231c.2.1
                have p231_2 := h231c.2.2.1
                have p231_3 := h231c.2.2.2
                linarith only [hlam, p231_0]
            · rcases h0bigk with h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h1, h173, h229, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h173, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h173, h230, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h0, hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h1, h173, h229, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h0, h173, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h0, h173, h230, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h1, hlam, p257_1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h4, hlam, p257_1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h173, h230, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h0, h173, h230, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h2, hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h5, hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h6, hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h173, h230, h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h3, hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p257_1, u1ehi1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h7, hlam, p257_0]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [h8, hlam, p257_1]
              · have p257_0 := h257c.1
                have p257_1 := h257c.2.1
                have p257_2 := h257c.2.2.1
                have p257_3 := h257c.2.2.2
                linarith only [hlam, p257_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h283 | h283
            · rcases h0bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h229, h4, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h229, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h229, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi4]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h0, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h229, h6, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h0, h229, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi4]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h1, hlam, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h4, hlam, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h229, h6, h9, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi4]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h2, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h5, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h6, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi4]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h3, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h7, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h8, hlam, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
            · rcases h0bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h229, h283, h4, h6, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h229, h283, h6, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h229, h283, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h229, h283, h3, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h0, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h229, h283, h6, h8, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h0, h229, h283, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h0, h229, h283, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h1, hlam, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h4, hlam, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h229, h283, h8, h9, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h0, h229, h283, h4, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h2, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h5, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h6, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h229, h283, h8, h9, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h3, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p310_1, u1ehi1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h7, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h8, hlam, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
      · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
        · rcases m.htr 1 3 4 (by decide) (by decide) with h338 | h338
          · rcases m.htr 1 4 5 (by decide) (by decide) with h339 | h339
            · linarith only [h2, h339, h8, hlam]
            · rcases h0bigk with h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h2, h4, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h2, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h2, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h0, hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h2, h7, h8, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h0, h2, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h1, hlam, p341_1]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h4, hlam, p341_1]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h0, h2, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h2, hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h5, hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h6, hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h8, hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h3, hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h0, h336, h338, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h7, hlam, p341_0]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [h2, h7, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p341_1, u1ehi3]
              · have p341_0 := h341c.1
                have p341_1 := h341c.2.1
                have p341_2 := h341c.2.2.1
                have p341_3 := h341c.2.2.2
                linarith only [hlam, p341_0]
          · linarith only [h338, h6, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · linarith only [h336, h337, h5, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
        · rcases m.htr 1 3 4 (by decide) (by decide) with h370 | h370
          · rcases m.htr 1 4 5 (by decide) (by decide) with h371 | h371
            · linarith only [h2, h371, h8, hlam]
            · rcases h0bigk with h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h336, h369, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h1, h336, h369, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi4]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h0, hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h1, h336, h369, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h0, h2, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h1, hlam, p373_1]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h4, hlam, p373_1]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h0, h2, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h2, hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h5, hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h6, hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h8, hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h3, hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h0, h369, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h7, hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [h2, h7, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p373_1, u1ehi3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
          · linarith only [h336, h369, h370, h6, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
        · linarith only [h369, h5, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h401 | h401
    · linarith only [h401, h6, h7, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
      · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
        · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
          · rcases m.htr 1 4 5 (by decide) (by decide) with h406 | h406
            · linarith only [h2, h401, h406, hlam]
            · rcases h0bigk with h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h0, h403, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p408_1]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h1, h405, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p408_1]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p408_1, u1ehi3]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h1, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p408_1, u1ehi2]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h0, hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p408_1, u1ehi2]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p408_1, u1ehi3]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h0, h2, h6, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p408_1, u1ehi3]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h1, hlam, p408_1]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h4, hlam, p408_1]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p408_1, u1ehi3]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h7, hlam, p408_1]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h2, hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h5, hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h6, hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h401, hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h3, hlam, p408_0]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h401, hc02, hc45, hlam, hphi, ht23, ht34, p408_1]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h401, hc03, hc45, hlam, hphi, ht34, p408_1]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [h2, h401, hc45, hlam, hphi, ht12, ht23, ht34, p408_1, u1ehi3]
              · have p408_0 := h408c.1
                have p408_1 := h408c.2.1
                have p408_2 := h408c.2.2.1
                have p408_3 := h408c.2.2.2
                linarith only [hlam, p408_0]
          · linarith only [h405, h6, h7, hc35, hlam, hphi, ht12, ht23, u1ehi2]
        · linarith only [h404, h5, h6, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h4, h403, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]

end R2N4
