import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_0_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
            · rcases h5bigk with h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h0, hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h0, h5, hc45, hlam, hphi, ht0b, ht5b, p7_1, u0elo0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h0, h6, hc45, hlam, hphi, ht0b, ht5b, p7_1, u0elo0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p7_1, u0elo0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h1, hlam, p7_1]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p7_1, u2elo4]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h1, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7_1, u2elo0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7_1, u2elo0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h2, hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h4, hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo4]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo4]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h3, hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p7_1, u2elo4]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h5, hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [h6, hlam, p7_0]
              · have p7_0 := h7c.1
                have p7_1 := h7c.2.1
                have p7_2 := h7c.2.2.1
                have p7_3 := h7c.2.2.2
                linarith only [hlam, p7_0]
            · rcases h5bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [hlam, p33_0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h2, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p33_1, u3elo0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h0, hlam, p33_0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [hlam, p33_0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h5, h6, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p33_1]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h0, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, p33_1, u0elo0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h0, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, p33_1, u0elo0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h1, hlam, p33_1]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p33_1, u2elo4]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [hlam, p33_0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h1, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p33_1, u2elo0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h1, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p33_1, u2elo0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h2, hlam, p33_0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h4, hlam, p33_0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo4]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [hlam, p33_0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h6, hlam, p33_1]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h3, hlam, p33_0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p33_1, u2elo4]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h5, hlam, p33_0]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p33_1, u2elo3]
              · have p33_0 := h33c.1
                have p33_1 := h33c.2.1
                have p33_2 := h33c.2.2.1
                have p33_3 := h33c.2.2.2
                linarith only [hlam, p33_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
            · rcases h5bigk with h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [hlam, p60_0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p60_1, u3elo0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p60_1, u3elo0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h2, h5, h59, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p60_1, u3elo0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h2, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p60_1, u3elo0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h0, hlam, p60_0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [hlam, p60_0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h0, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, p60_1, u0elo0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h5, h59, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p60_1]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h0, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, p60_1, u0elo0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h1, hlam, p60_1]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p60_1, u2elo4]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [hlam, p60_0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h5, h59, hlam, p60_1]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h5, hlam, p60_1]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h2, hlam, p60_0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h4, hlam, p60_0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p60_1, u3elo4]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [hlam, p60_0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h4, h5, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p60_1]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h3, hlam, p60_0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h3, hc15, hlam, hphi, ht0b, ht5b, p60_1, u0elo3]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h5, hc24, hc45, hlam, hphi, p60_1]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [h59, hlam, p60_0]
              · have p60_0 := h60c.1
                have p60_1 := h60c.2.1
                have p60_2 := h60c.2.2.1
                have p60_3 := h60c.2.2.2
                linarith only [hlam, p60_0]
            · rcases h5bigk with h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [hlam, p86_0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p86_1, u3elo0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h2, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p86_1, u3elo0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p86_1, u3elo0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h2, h59, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p86_1, u3elo0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h0, hlam, p86_0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [hlam, p86_0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h0, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, p86_1, u0elo0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h0, h59, hc34, hlam, hphi, ht0b, ht45, ht5b, p86_1, u0elo0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h0, h59, hc34, hlam, hphi, ht0b, ht45, ht5b, p86_1, u0elo0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h1, hlam, p86_1]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p86_1, u2elo4]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [hlam, p86_0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h59, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p86_1, u2elo4]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h5, hlam, p86_1]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h2, hlam, p86_0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h4, hlam, p86_0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p86_1, u3elo4]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [hlam, p86_0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h59, hlam, p86_1]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h3, hlam, p86_0]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h3, hc15, hlam, hphi, ht0b, ht5b, p86_1, u0elo3]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h3, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, p86_1, u0elo3]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [h3, hc35, hlam, hphi, ht0b, ht5b, p86_1, u0elo3]
              · have p86_0 := h86c.1
                have p86_1 := h86c.2.1
                have p86_2 := h86c.2.2.1
                have p86_3 := h86c.2.2.2
                linarith only [hlam, p86_0]
        · linarith only [h2, h4, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
        · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
          · linarith only [h1, h114, h3, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
            · linarith only [h0, h113, h116, h3, hlam]
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
                linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p118_1, u3elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h3, hlam, p118_1]
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
                linarith only [h0, h114, hc24, hlam, hphi, ht0b, ht45, ht5b, p118_1, u0elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h0, h116, hc34, hlam, hphi, ht0b, ht45, ht5b, p118_1, u0elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, p118_1, u0elo0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h1, hlam, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p118_1, u2elo4]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h1, h116, hc34, hlam, hphi, ht0b, ht45, ht5b, p118_1, u0elo4]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h114, hlam, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h2, hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h113, hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h113, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hlam, p118_0]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h116, hlam, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h3, hc04, hc45, hlam, hphi, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h113, h116, hc34, hc45, hlam, hphi, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h114, hc24, hc45, hlam, hphi, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [h116, hc34, hc45, hlam, hphi, p118_1]
              · have p118_0 := h118c.1
                have p118_1 := h118c.2.1
                have p118_2 := h118c.2.2.1
                have p118_3 := h118c.2.2.2
                linarith only [hlam, p118_0]
        · linarith only [h113, h2, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h145 | h145
      · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
        · linarith only [h146, h2, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h148 | h148
          · rcases m.htr 3 4 5 (by decide) (by decide) with h149 | h149
            · rcases h5bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [hlam, p150_0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p150_1, u0elo4]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p150_1, u2elo0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h2, hlam, p150_1]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h145, hc45, hlam, hphi, ht0b, ht5b, p150_1, u0elo3]
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
                linarith only [h0, h148, hc45, hlam, hphi, ht0b, ht5b, p150_1, u0elo0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h146, hlam, p150_1]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p150_1, u0elo0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h1, hlam, p150_1]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p150_1, u2elo4]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [hlam, p150_0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h1, h2, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p150_1, u2elo0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p150_1, u0elo4]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p150_1, u3elo4]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h146, hc13, hlam, hphi, p150_1, u3elo4]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h149, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p150_1, u3elo3]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [hlam, p150_0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h149, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p150_1, u3elo3]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h145, hlam, p150_0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h146, h148, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p150_1, u2elo3]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h148, hlam, p150_0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [h149, hlam, p150_0]
              · have p150_0 := h150c.1
                have p150_1 := h150c.2.1
                have p150_2 := h150c.2.2.1
                have p150_3 := h150c.2.2.2
                linarith only [hlam, p150_0]
            · linarith only [h1, h148, h149, h2, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
            · rcases h5bigk with h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [hlam, p178_0]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h146, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p178_1, u0elo4]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p178_1, u3elo4]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h2, hlam, p178_1]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h148, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p178_1, u3elo4]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h0, hlam, p178_0]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [hlam, p178_0]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h0, h148, hc24, hlam, hphi, ht0b, ht45, ht5b, p178_1, u0elo0]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h146, hlam, p178_1]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h0, h148, hc24, hlam, hphi, ht0b, ht45, ht5b, p178_1, u0elo0]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h1, hlam, p178_1]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p178_1, u2elo4]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [hlam, p178_0]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h2, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p178_1, u2elo4]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h148, hlam, p178_1]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p178_1, u3elo4]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h146, hc13, hlam, hphi, p178_1, u3elo4]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h177, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p178_1, u3elo3]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [hlam, p178_0]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h177, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p178_1, u3elo3]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h145, hlam, p178_0]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h145, h146, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p178_1, u0elo4]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h145, h148, hc24, hlam, hphi, ht0b, ht45, ht5b, p178_1, u0elo3]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [h177, hlam, p178_0]
              · have p178_0 := h178c.1
                have p178_1 := h178c.2.1
                have p178_2 := h178c.2.2.1
                have p178_3 := h178c.2.2.2
                linarith only [hlam, p178_0]
            · linarith only [h145, h177, h2, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h205 | h205
        · linarith only [h2, h205, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
          · linarith only [h1, h145, h207, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h209 | h209
            · rcases h5bigk with h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [hlam, p210_0]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h145, h205, h209, hc13, hlam, hphi, p210_1, u3elo3]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h145, h209, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p210_1, u3elo3]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h2, hlam, p210_1]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h145, hlam, p210_1]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h0, hlam, p210_0]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [hlam, p210_0]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h0, h207, hc24, hlam, hphi, ht0b, ht45, ht5b, p210_1, u0elo0]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h205, hlam, p210_1]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h0, h145, hlam, p210_1]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h1, hlam, p210_1]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p210_1, u2elo4]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [hlam, p210_0]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h1, h145, h2, h209, hc03, hlam, hphi, p210_1, u3elo3]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h207, hlam, p210_1]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p210_1, u3elo4]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h205, hc13, hlam, hphi, p210_1, u3elo4]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h207, h209, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p210_1, u3elo3]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [hlam, p210_0]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h145, h209, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p210_1, u3elo3]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h0, h205, hc13, hc45, hlam, hphi, ht34, p210_1]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h205, h209, hc13, hlam, hphi, p210_1, u3elo3]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h207, h209, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p210_1, u3elo3]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [h209, hlam, p210_0]
              · have p210_0 := h210c.1
                have p210_1 := h210c.2.1
                have p210_2 := h210c.2.2.1
                have p210_3 := h210c.2.2.2
                linarith only [hlam, p210_0]
            · rcases h5bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [hlam, p236_0]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h205, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1, u0elo4]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h1, h207, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p236_1, u2elo0]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h2, hlam, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h145, hlam, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h0, hlam, p236_0]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [hlam, p236_0]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h0, h207, hc24, hlam, hphi, ht0b, ht45, ht5b, p236_1, u0elo0]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h205, hlam, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h0, h209, hc34, hlam, hphi, ht0b, ht45, ht5b, p236_1, u0elo0]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h1, hlam, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p236_1, u2elo4]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [hlam, p236_0]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h1, h2, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p236_1, u2elo0]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h207, hlam, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p236_1, u3elo4]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h205, hc13, hlam, hphi, p236_1, u3elo4]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p236_1, u3elo4]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [hlam, p236_0]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h209, hlam, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h0, h205, hc13, hc45, hlam, hphi, ht34, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h205, hc13, hc45, hlam, hphi, ht34, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h207, hc24, hc45, hlam, hphi, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [h2, hc03, hc45, hlam, hphi, ht34, p236_1]
              · have p236_0 := h236c.1
                have p236_1 := h236c.2.1
                have p236_2 := h236c.2.2.1
                have p236_3 := h236c.2.2.2
                linarith only [hlam, p236_0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h262 | h262
    · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
      · rcases m.htr 1 3 5 (by decide) (by decide) with h264 | h264
        · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
          · rcases m.htr 3 4 5 (by decide) (by decide) with h266 | h266
            · rcases h5bigk with h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p267_1, u0elo4]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h1, hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h1, h265, h266, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, u2elo3]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h1, h265, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, u2elo3]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h0, hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p267_1]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p267_1, u0elo4]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p267_1, u0elo0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h265, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, u2elo3]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h265, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, u2elo3]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h265, h266, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, u2elo3]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h265, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, u2elo3]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h262, hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h264, hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h264, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p267_1]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h264, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p267_1]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h263, hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h263, hc15, hlam, hphi, ht0b, ht5b, p267_1, u0elo3]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h265, hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [h266, hlam, p267_0]
              · have p267_0 := h267c.1
                have p267_1 := h267c.2.1
                have p267_2 := h267c.2.2.1
                have p267_3 := h267c.2.2.2
                linarith only [hlam, p267_0]
            · rcases h5bigk with h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p293_1, u0elo4]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h1, hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h262, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p293_1, u3elo0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h262, h266, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p293_1, u3elo0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h0, hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p293_1]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h0, h266, hc34, hlam, hphi, ht0b, ht45, ht5b, p293_1, u0elo0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h0, h266, hc34, hlam, hphi, ht0b, ht45, ht5b, p293_1, u0elo0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p293_1, u2elo4]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h264, h265, h266, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u2elo3]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h265, h266, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u2elo3]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h265, h266, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u2elo3]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h262, hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h264, hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p293_1, u3elo4]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h266, hlam, p293_1]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h263, hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h263, hc15, hlam, hphi, ht0b, ht5b, p293_1, u0elo3]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h265, hlam, p293_0]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [h263, hc35, hlam, hphi, ht0b, ht5b, p293_1, u0elo4]
              · have p293_0 := h293c.1
                have p293_1 := h293c.2.1
                have p293_2 := h293c.2.2.1
                have p293_3 := h293c.2.2.2
                linarith only [hlam, p293_0]
          · linarith only [h1, h263, h265, hlam]
        · linarith only [h262, h264, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h321 | h321
        · rcases m.htr 2 4 5 (by decide) (by decide) with h322 | h322
          · rcases m.htr 3 4 5 (by decide) (by decide) with h323 | h323
            · linarith only [h0, h263, h321, h323, hlam]
            · rcases h5bigk with h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [hlam, p325_0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p325_1, u0elo4]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h1, hlam, p325_0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h262, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p325_1, u3elo0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h263, hlam, p325_1]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h0, hlam, p325_0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [hlam, p325_0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p325_1, u0elo0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h0, h263, h322, h323, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p325_1, u2elo3]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h0, h263, hlam, p325_1]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p325_1, u2elo4]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h321, h322, h323, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p325_1, u2elo3]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [hlam, p325_0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h322, h323, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p325_1, u2elo3]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h263, h322, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p325_1, u2elo3]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h262, hlam, p325_0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h321, hlam, p325_0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h321, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p325_1]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [hlam, p325_0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h323, hlam, p325_1]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p325_1]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h322, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p325_1, u2elo3]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h322, hlam, p325_0]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [h322, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p325_1, u2elo3]
              · have p325_0 := h325c.1
                have p325_1 := h325c.2.1
                have p325_2 := h325c.2.2.1
                have p325_3 := h325c.2.2.2
                linarith only [hlam, p325_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h351 | h351
            · linarith only [h1, h322, h351, hc02, hlam, hphi, ht23, u3elo3]
            · rcases h5bigk with h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h321, h351, hc34, hlam, hphi, ht0b, ht45, ht5b, p353_1, u0elo4]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h1, hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h351, hc34, hlam, hphi, ht0b, ht45, ht5b, p353_1, u0elo4]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h263, hlam, p353_1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h0, hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p353_1, u0elo0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h0, h351, hc34, hlam, hphi, ht0b, ht45, ht5b, p353_1, u0elo0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h0, h1, h322, hc05, hlam, hphi, ht0b, ht5b, p353_1, u0elo0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p353_1, u2elo4]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h321, h351, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p353_1, u2elo4]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h351, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p353_1, u2elo4]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h322, hlam, p353_1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h262, hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h321, hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p353_1, u3elo4]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h351, hlam, p353_1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p353_1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h321, h351, hc34, hc45, hlam, hphi, p353_1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p353_1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h351, hc34, hc45, hlam, hphi, p353_1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
        · linarith only [h262, h321, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h380 | h380
      · rcases m.htr 1 3 5 (by decide) (by decide) with h381 | h381
        · linarith only [h262, h381, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
          · rcases m.htr 3 4 5 (by decide) (by decide) with h384 | h384
            · rcases h5bigk with h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [hlam, p385_0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p385_1, u0elo4]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h1, hlam, p385_0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h262, hlam, p385_1]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p385_1, u0elo4]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h0, hlam, p385_0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [hlam, p385_0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p385_1, u0elo0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h381, hlam, p385_1]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p385_1, u0elo4]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p385_1, u2elo4]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h381, h383, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p385_1, u2elo3]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [hlam, p385_0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h383, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p385_1, u2elo3]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h383, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p385_1, u2elo3]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht23, p385_1, u3elo4]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h381, hc13, hlam, hphi, p385_1, u3elo4]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h384, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p385_1, u3elo3]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [hlam, p385_0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h384, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p385_1, u3elo3]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h380, hlam, p385_0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h381, hc13, hc45, hlam, hphi, ht34, p385_1]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h383, hlam, p385_0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [h384, hlam, p385_0]
              · have p385_0 := h385c.1
                have p385_1 := h385c.2.1
                have p385_2 := h385c.2.2.1
                have p385_3 := h385c.2.2.2
                linarith only [hlam, p385_0]
            · linarith only [h262, h380, h384, hlam]
          · linarith only [h1, h380, h383, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h413 | h413
        · linarith only [h262, h413, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
          · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
            · rcases h5bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h380, h416, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p417_1, u3elo3]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h1, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h262, hlam, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h380, hlam, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h0, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h413, hlam, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h0, h380, hlam, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p417_1, u2elo4]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h413, h415, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p417_1, u2elo3]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h262, h415, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p417_1, u2elo3]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h380, h415, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p417_1, u2elo3]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht23, p417_1, u3elo4]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h413, hc13, hlam, hphi, p417_1, u3elo4]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h416, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p417_1, u3elo3]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h380, h416, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p417_1, u3elo3]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h413, h416, hc13, hlam, hphi, p417_1, u3elo3]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h415, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h416, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hlam, p417_0]
            · rcases h5bigk with h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [hlam, p443_0]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h413, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p443_1, u0elo4]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h1, hlam, p443_0]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h262, hlam, p443_1]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h380, hlam, p443_1]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h0, hlam, p443_0]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [hlam, p443_0]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p443_1, u0elo0]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h413, hlam, p443_1]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h0, h262, h416, hlam, p443_1]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p443_1, u2elo4]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h413, h415, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p443_1, u2elo3]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [hlam, p443_0]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h262, h415, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p443_1, u2elo3]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h262, h415, h416, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p443_1, u2elo3]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht23, p443_1, u3elo4]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h413, hc13, hlam, hphi, p443_1, u3elo4]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h415, h416, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p443_1, u2elo3]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [hlam, p443_0]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h416, hlam, p443_1]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h1, h415, hc02, hlam, hphi, p443_1, u2elo3]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h413, h415, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p443_1, u2elo3]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h415, hlam, p443_0]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [h262, h415, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p443_1, u2elo3]
              · have p443_0 := h443c.1
                have p443_1 := h443c.2.1
                have p443_2 := h443c.2.2.1
                have p443_3 := h443c.2.2.2
                linarith only [hlam, p443_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h469 | h469
            · linarith only [h1, h415, h469, hc02, hlam, hphi, ht23, u3elo3]
            · rcases h5bigk with h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [hlam, p471_0]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h413, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1, u0elo4]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h1, hlam, p471_0]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h262, hlam, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h380, hlam, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h0, hlam, p471_0]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [hlam, p471_0]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h413, hlam, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h0, h1, h415, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p471_1, u0elo4]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p471_1, u2elo4]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h413, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p471_1, u2elo4]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [hlam, p471_0]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h262, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p471_1, u2elo4]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h415, hlam, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht23, p471_1, u3elo4]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h413, hc13, hlam, hphi, p471_1, u3elo4]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p471_1, u3elo4]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [hlam, p471_0]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h469, hlam, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h413, hc13, hc45, hlam, hphi, ht34, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [h262, hc03, hc45, hlam, hphi, ht34, p471_1]
              · have p471_0 := h471c.1
                have p471_1 := h471c.2.1
                have p471_2 := h471c.2.2.1
                have p471_3 := h471c.2.2.2
                linarith only [hlam, p471_0]

end R2N4
