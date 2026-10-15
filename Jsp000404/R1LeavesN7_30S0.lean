import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
    · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
          · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
            · rcases h0bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p12_1, u5ehi0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h8, hc01, hlam, hphi, ht0b, ht5b, p12_1, u5ehi3]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h9, hc01, hlam, hphi, ht0b, ht5b, p12_1, u5ehi4]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p12_1, u5ehi0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h0, hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h8, hc02, hlam, hphi, ht0b, ht5b, p12_1, u5ehi3]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht5b, p12_1, u5ehi4]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p12_1, u5ehi1]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h1, hlam, p12_1]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h4, hlam, p12_1]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h9, hc03, hlam, hphi, ht0b, ht5b, p12_1, u5ehi4]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht5b, p12_1, u5ehi1]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h2, hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h5, hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h7, hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht5b, p12_1, u5ehi1]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h3, hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h6, hlam, p12_1]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h8, hlam, p12_0]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [h9, hlam, p12_1]
              · have p12_0 := h12c.1
                have p12_1 := h12c.2.1
                have p12_2 := h12c.2.2.1
                have p12_3 := h12c.2.2.2
                linarith only [hlam, p12_0]
            · rcases h0bigk with h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h11, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h11, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h11, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p38_1, u5ehi1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h0, hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h11, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h0, h11, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p38_1, u5ehi1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h1, hlam, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h4, hlam, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h0, h11, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht5b, p38_1, u5ehi1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h2, hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h5, hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h7, hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht5b, p38_1, u5ehi1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h3, hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h6, hlam, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h8, hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h9, hlam, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
            · rcases h0bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h9, hc01, hlam, hphi, ht0b, ht5b, p65_1, u5ehi4]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p65_1, u5ehi1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h0, hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h8, hc02, hlam, hphi, ht0b, ht5b, p65_1, u5ehi3]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht5b, p65_1, u5ehi4]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p65_1, u5ehi1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h1, hlam, p65_1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h4, hlam, p65_1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht5b, p65_1, u5ehi4]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht5b, p65_1, u5ehi1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h2, hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h5, hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h7, hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht5b, p65_1, u5ehi1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h3, hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h6, hlam, p65_1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h8, hlam, p65_0]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [h9, hlam, p65_1]
              · have p65_0 := h65c.1
                have p65_1 := h65c.2.1
                have p65_2 := h65c.2.2.1
                have p65_3 := h65c.2.2.2
                linarith only [hlam, p65_0]
            · rcases h0bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h4, h64, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p91_1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h64, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p91_1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h9, hc01, hlam, hphi, ht0b, ht5b, p91_1, u5ehi4]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p91_1, u5ehi1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h0, hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h8, hc02, hlam, hphi, ht0b, ht5b, p91_1, u5ehi3]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht5b, p91_1, u5ehi4]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p91_1, u5ehi1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h1, hlam, p91_1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h4, hlam, p91_1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h9, hc03, hlam, hphi, ht0b, ht5b, p91_1, u5ehi4]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht5b, p91_1, u5ehi1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h2, hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h5, hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h7, hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht5b, p91_1, u5ehi1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h3, hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h6, hlam, p91_1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h8, hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h9, hlam, p91_1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
          · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
            · rcases h0bigk with h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h118, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p119_1]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h118, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p119_1]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                rcases p119_3 (m.d 0 1) (by simp) with h123 | h123
                · rcases p119_3 (m.d 0 2) (by simp) with h124 | h124
                  · linarith only [h0, h124, hlam]
                  · linarith only [h124, h5, hlam]
                · linarith only [h123, h2, hlam]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p119_1, u5ehi1]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h0, hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h8, hc02, hlam, hphi, ht0b, ht5b, p119_1, u5ehi3]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                rcases p119_3 (m.d 0 1) (by simp) with h132 | h132
                · rcases p119_3 (m.d 0 2) (by simp) with h133 | h133
                  · rcases p119_3 (m.d 0 3) (by simp) with h134 | h134
                    · linarith only [h134, h4, hlam]
                    · linarith only [h134, h7, hlam]
                  · linarith only [h133, h5, hlam]
                · linarith only [h132, h2, hlam]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p119_1, u5ehi1]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h1, hlam, p119_1]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h4, hlam, p119_1]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                rcases p119_3 (m.d 0 1) (by simp) with h143 | h143
                · rcases p119_3 (m.d 0 2) (by simp) with h144 | h144
                  · rcases p119_3 (m.d 0 3) (by simp) with h145 | h145
                    · rcases p119_3 (m.d 0 4) (by simp) with h146 | h146
                      · linarith only [h146, h7, hlam]
                      · rcases p119_3 (m.d 0 5) (by simp) with h148 | h148
                        · linarith only [h148, h8, hlam]
                        · linarith only [h148, h9, hlam]
                    · linarith only [h145, h7, hlam]
                  · linarith only [h144, h5, hlam]
                · linarith only [h143, h2, hlam]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h3, hc03, hlam, hphi, ht0b, ht5b, p119_1, u5ehi1]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h2, hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h5, hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h7, hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h9, hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h3, hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h6, hlam, p119_1]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h8, hlam, p119_0]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [h118, h5, h9, hc34, hc45, hlam, hphi, p119_1]
              · have p119_0 := h119c.1
                have p119_1 := h119c.2.1
                have p119_2 := h119c.2.2.1
                have p119_3 := h119c.2.2.2
                linarith only [hlam, p119_0]
            · rcases h0bigk with h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h118, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p165_1, u5ehi0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h0, hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h118, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h0, h118, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p165_1, u5ehi1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h1, hlam, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h4, hlam, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h118, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht5b, p165_1, u5ehi1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h2, hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h5, hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h7, hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h9, hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h3, hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h6, hlam, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h8, hlam, p165_0]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [h118, h7, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1]
              · have p165_0 := h165c.1
                have p165_1 := h165c.2.1
                have p165_2 := h165c.2.2.1
                have p165_3 := h165c.2.2.2
                linarith only [hlam, p165_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
            · rcases h0bigk with h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p192_1]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h191, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p192_1]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                rcases p192_3 (m.d 0 1) (by simp) with h196 | h196
                · rcases p192_3 (m.d 0 2) (by simp) with h197 | h197
                  · linarith only [h0, h197, hlam]
                  · linarith only [h197, h5, hlam]
                · linarith only [h196, h2, hlam]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p192_1, u5ehi0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h0, hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h8, hc02, hlam, hphi, ht0b, ht5b, p192_1, u5ehi3]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                rcases p192_3 (m.d 0 1) (by simp) with h205 | h205
                · rcases p192_3 (m.d 0 2) (by simp) with h206 | h206
                  · rcases p192_3 (m.d 0 3) (by simp) with h207 | h207
                    · linarith only [h207, h4, hlam]
                    · linarith only [h207, h7, hlam]
                  · linarith only [h206, h5, hlam]
                · linarith only [h2, h205, hlam]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p192_1, u5ehi1]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h1, hlam, p192_1]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h4, hlam, p192_1]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                rcases p192_3 (m.d 0 1) (by simp) with h216 | h216
                · rcases p192_3 (m.d 0 2) (by simp) with h217 | h217
                  · rcases p192_3 (m.d 0 3) (by simp) with h218 | h218
                    · rcases p192_3 (m.d 0 4) (by simp) with h219 | h219
                      · linarith only [h219, h7, hlam]
                      · rcases p192_3 (m.d 0 5) (by simp) with h221 | h221
                        · linarith only [h221, h8, hlam]
                        · linarith only [h221, h9, hlam]
                    · linarith only [h218, h7, hlam]
                  · linarith only [h217, h5, hlam]
                · linarith only [h2, h216, hlam]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h3, hc03, hlam, hphi, ht0b, ht5b, p192_1, u5ehi1]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h2, hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h5, hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h7, hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h9, hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h3, hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h6, hlam, p192_1]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h8, hlam, p192_0]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [h191, h5, h9, hc34, hc45, hlam, hphi, p192_1]
              · have p192_0 := h192c.1
                have p192_1 := h192c.2.1
                have p192_2 := h192c.2.2.1
                have p192_3 := h192c.2.2.2
                linarith only [hlam, p192_0]
            · linarith only [h117, h191, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
        · linarith only [h239, h7, h8, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h241 | h241
          · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
            · rcases h0bigk with h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h0, h241, h242, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h242, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                rcases p243_3 (m.d 0 1) (by simp) with h247 | h247
                · rcases p243_3 (m.d 0 2) (by simp) with h248 | h248
                  · linarith only [h0, h248, hlam]
                  · linarith only [h248, h5, hlam]
                · linarith only [h2, h247, hlam]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p243_1, u5ehi0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h0, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h1, h241, h242, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                rcases p243_3 (m.d 0 1) (by simp) with h256 | h256
                · rcases p243_3 (m.d 0 2) (by simp) with h257 | h257
                  · rcases p243_3 (m.d 0 3) (by simp) with h258 | h258
                    · linarith only [h258, h4, hlam]
                    · linarith only [h258, h7, hlam]
                  · linarith only [h257, h5, hlam]
                · linarith only [h2, h256, hlam]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h0, h1, h241, h242, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h1, hlam, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h4, hlam, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h2, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h8, hlam, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h2, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h5, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h7, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h239, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h3, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h6, hlam, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h1, h241, h242, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h2, h239, hc14, hc45, hlam, hphi, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
            · linarith only [h242, h7, h8, hc23, hc35, hlam, hphi]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
            · rcases h0bigk with h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h241, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h241, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                rcases p281_3 (m.d 0 1) (by simp) with h285 | h285
                · rcases p281_3 (m.d 0 2) (by simp) with h286 | h286
                  · linarith only [h0, h286, hlam]
                  · linarith only [h286, h5, hlam]
                · linarith only [h2, h285, hlam]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p281_1, u5ehi0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h0, hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h241, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                rcases p281_3 (m.d 0 1) (by simp) with h294 | h294
                · rcases p281_3 (m.d 0 2) (by simp) with h295 | h295
                  · rcases p281_3 (m.d 0 3) (by simp) with h296 | h296
                    · linarith only [h296, h4, hlam]
                    · linarith only [h296, h7, hlam]
                  · linarith only [h295, h5, hlam]
                · linarith only [h2, h294, hlam]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h0, h241, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h1, hlam, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h4, hlam, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h280, h5, h8, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h8, hlam, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h2, hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h5, hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h7, hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h239, hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h3, hlam, p281_0]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h6, hlam, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h241, h3, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [h239, h280, h5, hc34, hc45, hlam, hphi, p281_1]
              · have p281_0 := h281c.1
                have p281_1 := h281c.2.1
                have p281_2 := h281c.2.2.1
                have p281_3 := h281c.2.2.2
                linarith only [hlam, p281_0]
            · linarith only [h241, h280, h7, h8, hc12, hc35, hlam, hphi, ht23]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h318 | h318
      · rcases m.htr 0 4 5 (by decide) (by decide) with h319 | h319
        · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
          · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
            · linarith only [h318, h320, h321, h7, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
            · rcases h0bigk with h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h320, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h318, hc01, hlam, hphi, ht0b, ht5b, p323_1, u5ehi3]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h318, h7, hc01, hlam, hphi, ht0b, ht5b, p323_1, u5ehi3]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p323_1, u5ehi1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h318, hc02, hlam, hphi, ht0b, ht5b, p323_1, u5ehi3]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h318, h7, hc01, hlam, hphi, ht0b, ht5b, p323_1, u5ehi3]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p323_1, u5ehi1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h1, hlam, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h4, hlam, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h7, hlam, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h3, hc03, hlam, hphi, ht0b, ht5b, p323_1, u5ehi1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h2, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h5, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h7, hc03, hc34, hlam, hphi, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p323_1, u5ehi1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h3, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h6, hlam, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h318, hlam, p323_0]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [h319, hlam, p323_1]
              · have p323_0 := h323c.1
                have p323_1 := h323c.2.1
                have p323_2 := h323c.2.2.1
                have p323_3 := h323c.2.2.2
                linarith only [hlam, p323_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
            · linarith only [h349, h4, h7, hlam]
            · rcases h0bigk with h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [hlam, p351_0]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p351_1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h318, hc01, hlam, hphi, ht0b, ht5b, p351_1, u5ehi3]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h318, h7, hc01, hlam, hphi, ht0b, ht5b, p351_1, u5ehi3]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p351_1, u5ehi1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h0, hlam, p351_0]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [hlam, p351_0]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h318, hc02, hlam, hphi, ht0b, ht5b, p351_1, u5ehi3]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h0, h318, h7, hc01, hlam, hphi, ht0b, ht5b, p351_1, u5ehi3]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p351_1, u5ehi1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h1, hlam, p351_1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h4, hlam, p351_1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [hlam, p351_0]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h7, hlam, p351_1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h3, hc03, hlam, hphi, ht0b, ht5b, p351_1, u5ehi1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h2, hlam, p351_0]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h5, hlam, p351_0]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h1, h320, h7, hc12, hc34, hlam, hphi, ht23, p351_1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [hlam, p351_0]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p351_1, u5ehi1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h3, hlam, p351_0]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h6, hlam, p351_1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h318, hlam, p351_0]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [h319, hlam, p351_1]
              · have p351_0 := h351c.1
                have p351_1 := h351c.2.1
                have p351_2 := h351c.2.2.1
                have p351_3 := h351c.2.2.2
                linarith only [hlam, p351_0]
        · linarith only [h318, h319, h7, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h378 | h378
        · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
          · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
            · linarith only [h0, h379, h380, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases h0bigk with h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h378, h5, hc01, hlam, hphi, ht0b, ht5b, p382_1, u5ehi4]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                rcases p382_3 (m.d 0 1) (by simp) with h385 | h385
                · rcases p382_3 (m.d 0 2) (by simp) with h386 | h386
                  · linarith only [h0, h386, hlam]
                  · linarith only [h386, h4, hlam]
                · linarith only [h1, h385, hlam]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h378, hc01, hlam, hphi, ht0b, ht5b, p382_1, u5ehi4]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p382_1, u5ehi1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h0, hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                rcases p382_3 (m.d 0 1) (by simp) with h394 | h394
                · rcases p382_3 (m.d 0 2) (by simp) with h395 | h395
                  · rcases p382_3 (m.d 0 3) (by simp) with h396 | h396
                    · linarith only [h396, h4, hlam]
                    · rcases p382_3 (m.d 0 4) (by simp) with h398 | h398
                      · linarith only [h398, h5, hlam]
                      · linarith only [h398, h7, hlam]
                  · linarith only [h395, h4, hlam]
                · linarith only [h1, h394, hlam]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h378, hc02, hlam, hphi, ht0b, ht5b, p382_1, u5ehi4]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p382_1, u5ehi1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h1, hlam, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h4, hlam, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h7, hlam, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h318, hlam, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h2, hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h5, hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h1, h379, h7, hc23, hc34, hlam, hphi, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p382_1, u5ehi1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h3, hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h6, hlam, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h1, h318, h379, hc23, hc35, hlam, hphi, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h378, hlam, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h420 | h420
            · linarith only [h4, h420, h7, hlam]
            · rcases h0bigk with h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [hlam, p422_0]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h378, h5, hc01, hlam, hphi, ht0b, ht5b, p422_1, u5ehi0]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h379, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h378, hc01, hlam, hphi, ht0b, ht5b, p422_1, u5ehi4]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p422_1, u5ehi1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h0, hlam, p422_0]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [hlam, p422_0]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h379, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h0, h378, hc01, hlam, hphi, ht0b, ht5b, p422_1, u5ehi4]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p422_1, u5ehi1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h1, hlam, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h4, hlam, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [hlam, p422_0]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h7, hlam, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h318, hlam, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h2, hlam, p422_0]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h5, hlam, p422_0]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h379, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [hlam, p422_0]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h318, h379, h4, h7, hc12, hc34, hlam, hphi, ht23, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h3, hlam, p422_0]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h6, hlam, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h379, h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [h378, hlam, p422_1]
              · have p422_0 := h422c.1
                have p422_1 := h422c.2.1
                have p422_2 := h422c.2.2.1
                have p422_3 := h422c.2.2.2
                linarith only [hlam, p422_0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h448 | h448
          · rcases m.htr 2 3 4 (by decide) (by decide) with h449 | h449
            · linarith only [h1, h448, h449, h7, hlam]
            · rcases h0bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h0, h448, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                rcases p451_3 (m.d 0 1) (by simp) with h454 | h454
                · rcases p451_3 (m.d 0 2) (by simp) with h455 | h455
                  · linarith only [h0, h455, hlam]
                  · linarith only [h4, h455, hlam]
                · linarith only [h1, h454, hlam]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                rcases p451_3 (m.d 0 1) (by simp) with h459 | h459
                · rcases p451_3 (m.d 0 2) (by simp) with h460 | h460
                  · linarith only [h0, h460, hlam]
                  · linarith only [h460, h5, hlam]
                · linarith only [h2, h459, hlam]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p451_1, u5ehi0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h0, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                rcases p451_3 (m.d 0 1) (by simp) with h467 | h467
                · rcases p451_3 (m.d 0 2) (by simp) with h468 | h468
                  · rcases p451_3 (m.d 0 3) (by simp) with h469 | h469
                    · linarith only [h4, h469, hlam]
                    · rcases p451_3 (m.d 0 4) (by simp) with h471 | h471
                      · linarith only [h471, h5, hlam]
                      · linarith only [h471, h7, hlam]
                  · linarith only [h4, h468, hlam]
                · linarith only [h1, h467, hlam]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                rcases p451_3 (m.d 0 1) (by simp) with h476 | h476
                · rcases p451_3 (m.d 0 2) (by simp) with h477 | h477
                  · rcases p451_3 (m.d 0 3) (by simp) with h478 | h478
                    · linarith only [h4, h478, hlam]
                    · rcases p451_3 (m.d 0 4) (by simp) with h480 | h480
                      · linarith only [h480, h5, hlam]
                      · rcases p451_3 (m.d 0 5) (by simp) with h482 | h482
                        · linarith only [h482, h6, hlam]
                        · linarith only [h378, h482, hlam]
                  · linarith only [h477, h5, hlam]
                · linarith only [h2, h476, hlam]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p451_1, u5ehi1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h1, hlam, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h4, hlam, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h7, hlam, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h318, hlam, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h2, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h5, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h1, h448, h7, hc23, hc34, hlam, hphi, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h378, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h3, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h6, hlam, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h1, h318, h448, hc23, hc35, hlam, hphi, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h378, hc04, hc45, hlam, hphi, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h503 | h503
            · linarith only [h4, h503, h7, hlam]
            · rcases h0bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [hlam, p505_0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h4, h448, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h4, h448, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h4, h448, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p505_1, u5ehi0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h0, hlam, p505_0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [hlam, p505_0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h4, h448, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h0, h4, h448, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p505_1, u5ehi1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h1, hlam, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h4, hlam, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [hlam, p505_0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h7, hlam, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h318, hlam, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h2, hlam, p505_0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h5, hlam, p505_0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h4, h448, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [hlam, p505_0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h378, hlam, p505_0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h3, hlam, p505_0]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h6, hlam, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h4, h448, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [h378, hc04, hc45, hlam, hphi, p505_1]
              · have p505_0 := h505c.1
                have p505_1 := h505c.2.1
                have p505_2 := h505c.2.2.1
                have p505_3 := h505c.2.2.2
                linarith only [hlam, p505_0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h531 | h531
    · rcases m.htr 0 3 5 (by decide) (by decide) with h532 | h532
      · linarith only [h4, h532, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h534 | h534
        · linarith only [h4, h531, h534, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h536 | h536
          · rcases m.htr 2 3 4 (by decide) (by decide) with h537 | h537
            · rcases h0bigk with h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h1, h4, h536, h537, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h1, h536, h537, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                rcases p538_3 (m.d 0 1) (by simp) with h542 | h542
                · rcases p538_3 (m.d 0 2) (by simp) with h543 | h543
                  · linarith only [h0, h543, hlam]
                  · linarith only [h5, h543, hlam]
                · linarith only [h2, h542, hlam]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h0, h536, h537, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h0, hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h1, h536, h537, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h534, h6, hc04, hc45, hlam, hphi, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h6, hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h1, hlam, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h4, hlam, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h4, h5, h6, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h532, hlam, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h2, hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h5, hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h531, hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h534, hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h3, hlam, p538_0]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h534, hc02, hc45, hlam, hphi, ht23, ht34, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h534, hc03, hc45, hlam, hphi, ht34, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [h5, h534, hc24, hc45, hlam, hphi, p538_1]
              · have p538_0 := h538c.1
                have p538_1 := h538c.2.1
                have p538_2 := h538c.2.2.1
                have p538_3 := h538c.2.2.2
                linarith only [hlam, p538_0]
            · linarith only [h531, h532, h537, hc23, hc35, hlam, hphi]
          · linarith only [h4, h536, h6, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h570 | h570
      · linarith only [h5, h531, h570, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h572 | h572
        · linarith only [h5, h572, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
          · rcases m.htr 2 3 4 (by decide) (by decide) with h575 | h575
            · linarith only [h0, h531, h574, h575, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases h0bigk with h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                rcases p577_3 (m.d 0 1) (by simp) with h580 | h580
                · rcases p577_3 (m.d 0 2) (by simp) with h581 | h581
                  · linarith only [h0, h581, hlam]
                  · linarith only [h4, h581, hlam]
                · linarith only [h1, h580, hlam]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                rcases p577_3 (m.d 0 1) (by simp) with h585 | h585
                · rcases p577_3 (m.d 0 2) (by simp) with h586 | h586
                  · linarith only [h0, h586, hlam]
                  · linarith only [h5, h586, hlam]
                · linarith only [h2, h585, hlam]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h5, h575, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h0, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h1, h570, h574, h6, hc23, hc35, hlam, hphi, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h5, h570, h575, h6, hc23, hc35, hlam, hphi, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h6, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h1, hlam, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h4, hlam, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h531, hlam, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h570, hlam, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h2, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h5, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h1, h5, h574, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h572, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h3, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h570, hc02, hc35, hlam, hphi, ht23, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h1, h570, h574, hc23, hc35, hlam, hphi, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h572, hc04, hc45, hlam, hphi, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
          · linarith only [h4, h574, h6, hc12, hc25, hlam, hphi]

end R2N4
