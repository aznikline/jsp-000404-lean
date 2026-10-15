import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_25_L_0_L_0_H_I_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
      · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
            · rcases h5bigk with h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u2elo0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u2elo0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h1, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u2elo0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u2elo0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h0, hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h0, h5, h7, hc45, hlam, hphi, ht0b, ht5b, p8_1, u0elo0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h0, h7, hc45, hlam, hphi, ht0b, ht5b, p8_1, u0elo0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p8_1, u0elo0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h1, hlam, p8_1]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h3, hlam, p8_1]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u2elo4]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u2elo0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h2, hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h4, hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h5, hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p8_1, u0elo2]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h6, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u2elo3]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h3, h5, h7, hlam, p8_1]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h6, hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h7, hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
            · rcases h5bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [hlam, p34_0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p34_1, u0elo4]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p34_1, u2elo0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p34_1, u2elo0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h1, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p34_1, u2elo0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h0, hlam, p34_0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [hlam, p34_0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h6, h7, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p34_1]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h0, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p34_1, u0elo0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h0, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p34_1, u0elo0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h1, hlam, p34_1]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h3, hlam, p34_1]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [hlam, p34_0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p34_1, u2elo4]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h1, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p34_1, u2elo0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h2, hlam, p34_0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h4, hlam, p34_0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h5, hlam, p34_0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [hlam, p34_0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h7, hlam, p34_1]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h2, h7, hc34, hc45, hlam, hphi, p34_1]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h3, h6, hlam, p34_1]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h6, hlam, p34_0]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [h0, h3, h6, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p34_1, u0elo4]
              · have p34_0 := h34c.1
                have p34_1 := h34c.2.1
                have p34_2 := h34c.2.2.1
                have p34_3 := h34c.2.2.2
                linarith only [hlam, p34_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
            · linarith only [h5, h6, h60, hlam]
            · rcases h5bigk with h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [hlam, p62_0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p62_1, u2elo0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p62_1, u2elo0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p62_1, u2elo0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h1, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p62_1, u2elo0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h0, hlam, p62_0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [hlam, p62_0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h0, h5, h60, hc34, hlam, hphi, ht0b, ht45, ht5b, p62_1, u0elo0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h0, h60, hc34, hlam, hphi, ht0b, ht45, ht5b, p62_1, u0elo0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h0, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, p62_1, u0elo0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h1, hlam, p62_1]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h3, hlam, p62_1]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [hlam, p62_0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h60, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p62_1, u2elo4]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h6, hlam, p62_1]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h2, hlam, p62_0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h4, hlam, p62_0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h5, hlam, p62_0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [hlam, p62_0]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h60, hlam, p62_1]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h2, h60, hc34, hc45, hlam, hphi, p62_1]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h3, h5, h60, hc34, hc45, hlam, hphi, p62_1]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h5, h60, hc34, hc45, hlam, hphi, p62_1]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [h60, hc34, hc45, hlam, hphi, p62_1]
              · have p62_0 := h62c.1
                have p62_1 := h62c.2.1
                have p62_2 := h62c.2.2.1
                have p62_3 := h62c.2.2.2
                linarith only [hlam, p62_0]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h88 | h88
          · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
            · rcases h5bigk with h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [hlam, p90_0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p90_1, u0elo4]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p90_1, u2elo0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h1, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p90_1, u2elo0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p90_1, u2elo0]
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
                linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p90_1, u0elo0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p90_1, u0elo0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p90_1, u0elo0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h1, hlam, p90_1]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h3, hlam, p90_1]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [hlam, p90_0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h5, hlam, p90_1]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p90_1, u2elo4]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h2, hlam, p90_0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h4, hlam, p90_0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h2, hc25, hlam, hphi, ht0b, ht5b, p90_1, u0elo2]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [hlam, p90_0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h0, h4, hc45, hlam, hphi, ht0b, ht5b, p90_1, u0elo0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h1, h5, hc23, hc45, hlam, hphi, ht34, p90_1]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h4, h5, h88, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p90_1, u2elo4]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h88, hlam, p90_0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [h89, hlam, p90_0]
              · have p90_0 := h90c.1
                have p90_1 := h90c.2.1
                have p90_2 := h90c.2.2.1
                have p90_3 := h90c.2.2.2
                linarith only [hlam, p90_0]
            · linarith only [h5, h88, h89, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
            · rcases h5bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p118_1, u0elo4]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p118_1, u2elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h1, h117, h88, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p118_1, u2elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h1, h88, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p118_1, u2elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h0, hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u0elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h0, h117, h88, hc24, hlam, hphi, ht0b, ht45, ht5b, p118_1, u0elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h0, h88, hc24, hlam, hphi, ht0b, ht45, ht5b, p118_1, u0elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h1, hlam, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h3, hlam, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h5, hlam, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h88, hlam, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h2, hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h4, hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h5, hc23, hc35, hlam, hphi, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h0, h4, h88, hc24, hlam, hphi, ht0b, ht45, ht5b, p118_1, u0elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h117, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h117, h4, hlam, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h0, h117, h4, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u0elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h117, hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hlam, p118_0]
            · rcases h5bigk with h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [hlam, p144_0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p144_1, u0elo4]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h1, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p144_1, u2elo0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h1, h117, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h0, hlam, p144_0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [hlam, p144_0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p144_1, u0elo0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p144_1, u0elo0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h0, h117, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p144_1, u0elo0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h1, hlam, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h3, hlam, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [hlam, p144_0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h5, hlam, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h88, hlam, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h2, hlam, p144_0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h4, hlam, p144_0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h5, hc23, hc35, hlam, hphi, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [hlam, p144_0]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h117, hlam, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h1, h5, hc23, hc45, hlam, hphi, ht34, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h4, h5, hc23, hc45, hlam, hphi, ht34, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h5, hc23, hc45, hlam, hphi, ht34, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [h5, hc23, hc45, hlam, hphi, ht34, p144_1]
              · have p144_0 := h144c.1
                have p144_1 := h144c.2.1
                have p144_2 := h144c.2.2.1
                have p144_3 := h144c.2.2.2
                linarith only [hlam, p144_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
        · linarith only [h170, h3, h4, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h172 | h172
          · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
            · rcases h5bigk with h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [hlam, p174_0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p174_1, u2elo0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p174_1, u2elo0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h1, h170, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p174_1, u2elo0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p174_1, u2elo0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h0, hlam, p174_0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [hlam, p174_0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h0, h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p174_1, u0elo0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h4, hlam, p174_1]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p174_1, u0elo0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h1, hlam, p174_1]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h3, hlam, p174_1]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [hlam, p174_0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h170, hlam, p174_1]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p174_1, u2elo4]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h2, hlam, p174_0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p174_1, u0elo2]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h2, hc25, hlam, hphi, ht0b, ht5b, p174_1, u0elo2]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [hlam, p174_0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p174_1, u0elo2]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h172, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p174_1, u2elo3]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h172, h3, hlam, p174_1]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h172, hlam, p174_0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [h173, hlam, p174_0]
              · have p174_0 := h174c.1
                have p174_1 := h174c.2.1
                have p174_2 := h174c.2.2.1
                have p174_3 := h174c.2.2.2
                linarith only [hlam, p174_0]
            · linarith only [h172, h173, h3, h4, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
            · rcases h5bigk with h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p202_1, u0elo4]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p202_1, u2elo0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h1, h172, h201, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p202_1, u2elo0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h1, h172, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p202_1, u2elo0]
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
                linarith only [h0, h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p202_1, u0elo0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h4, hlam, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h172, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h1, hlam, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h3, hlam, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h170, hlam, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h172, hlam, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h2, hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p202_1, u0elo2]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h170, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p202_1, u0elo2]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h172, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, p202_1, u0elo2]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h0, h170, h3, hc23, hc45, hlam, hphi, ht34, p202_1]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h170, h2, h201, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p202_1, u0elo2]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h170, h2, h201, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p202_1, u0elo2]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [h201, hlam, p202_0]
              · have p202_0 := h202c.1
                have p202_1 := h202c.2.1
                have p202_2 := h202c.2.2.1
                have p202_3 := h202c.2.2.2
                linarith only [hlam, p202_0]
            · rcases h5bigk with h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [hlam, p228_0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h170, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p228_1, u0elo4]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h1, h170, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p228_1, u2elo0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p228_1, u2elo0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h1, h201, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p228_1, u2elo0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h0, hlam, p228_0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [hlam, p228_0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h0, h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p228_1, u0elo0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h4, hlam, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h201, h4, hlam, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h1, hlam, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h3, hlam, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [hlam, p228_0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h170, hlam, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h172, hlam, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h2, hlam, p228_0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p228_1, u0elo2]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h170, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p228_1, u0elo2]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [hlam, p228_0]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h201, hlam, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h0, h170, h3, hc23, hc45, hlam, hphi, ht34, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h170, h3, hc23, hc45, hlam, hphi, ht34, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h170, hc23, hc45, hlam, hphi, ht34, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [h4, hc13, hc45, hlam, hphi, ht34, p228_1]
              · have p228_0 := h228c.1
                have p228_1 := h228c.2.1
                have p228_2 := h228c.2.2.1
                have p228_3 := h228c.2.2.2
                linarith only [hlam, p228_0]
    · linarith only [h1, h3, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
    · rcases m.htr 1 3 5 (by decide) (by decide) with h256 | h256
      · linarith only [h0, h2, h256, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h258 | h258
        · linarith only [h0, h2, h255, h258, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
          · rcases m.htr 3 4 5 (by decide) (by decide) with h261 | h261
            · rcases h5bigk with h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [hlam, p262_0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p262_1, u0elo4]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p262_1, u2elo0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h2, hlam, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p262_1, u2elo0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h0, hlam, p262_0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [hlam, p262_0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h0, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p262_1, u0elo0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h256, hlam, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p262_1, u0elo0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h1, hlam, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h255, hlam, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [hlam, p262_0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h258, hlam, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p262_1, u2elo4]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h2, h261, hc03, hc34, hlam, hphi, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h256, h261, hc13, hc34, hlam, hphi, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h258, h261, hc23, hc34, hlam, hphi, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [hlam, p262_0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                rcases p262_3 (m.d 0 5) (by simp) with h282 | h282
                · linarith only [h2, h282, hlam]
                · linarith only [h0, h255, h260, h282, hlam]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h0, h255, h260, hlam, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h255, h260, hlam, p262_1]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h260, hlam, p262_0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [h261, hlam, p262_0]
              · have p262_0 := h262c.1
                have p262_1 := h262c.2.1
                have p262_2 := h262c.2.2.1
                have p262_3 := h262c.2.2.2
                linarith only [hlam, p262_0]
            · linarith only [h0, h2, h255, h260, h261, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h291 | h291
            · rcases h5bigk with h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [hlam, p292_0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p292_1, u0elo4]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p292_1, u2elo0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h2, hlam, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p292_1, u2elo0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h0, hlam, p292_0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [hlam, p292_0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h0, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p292_1, u0elo0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h256, hlam, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h0, h260, hc24, hlam, hphi, ht0b, ht45, ht5b, p292_1, u0elo0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h1, hlam, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h255, hlam, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [hlam, p292_0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h258, hlam, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h260, hlam, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h1, h258, h291, hc23, hc34, hlam, hphi, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h255, h258, h291, hc23, hc34, hlam, hphi, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h258, h291, hc23, hc34, hlam, hphi, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [hlam, p292_0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h260, h291, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h0, h255, h258, hc23, hc45, hlam, hphi, ht34, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h255, h258, h291, hc23, hc34, hlam, hphi, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h258, h291, hc23, hc34, hlam, hphi, p292_1]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [h291, hlam, p292_0]
              · have p292_0 := h292c.1
                have p292_1 := h292c.2.1
                have p292_2 := h292c.2.2.1
                have p292_3 := h292c.2.2.2
                linarith only [hlam, p292_0]
            · rcases h5bigk with h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [hlam, p318_0]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h255, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p318_1, u0elo4]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h1, h258, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p318_1, u2elo0]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h2, hlam, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h1, h291, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p318_1, u2elo0]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h0, hlam, p318_0]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [hlam, p318_0]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h0, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p318_1, u0elo0]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h256, hlam, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h0, h2, h291, hlam, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h1, hlam, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h255, hlam, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [hlam, p318_0]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h258, hlam, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h260, hlam, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h1, h258, hc23, hc35, hlam, hphi, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h255, h258, h291, hc23, hc45, hlam, hphi, ht34, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h258, h291, hc23, hc45, hlam, hphi, ht34, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [hlam, p318_0]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h291, hlam, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h0, h255, h258, hc23, hc45, hlam, hphi, ht34, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h255, h258, hc23, hc45, hlam, hphi, ht34, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h258, hc23, hc45, hlam, hphi, ht34, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [h2, hc03, hc45, hlam, hphi, ht34, p318_1]
              · have p318_0 := h318c.1
                have p318_1 := h318c.2.1
                have p318_2 := h318c.2.2.1
                have p318_3 := h318c.2.2.2
                linarith only [hlam, p318_0]
    · linarith only [h1, h255, hc12, hlam, hphi, u2elo0]

end R2N4
