import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_0_L_0_L_0_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                  · rcases h5bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h7, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p10_1, u2elo4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h4, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10_1, u2elo4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h5, hc05, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo2]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h5, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h7, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h4, h6, h7, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1, u1elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h6, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h8, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h9, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                  · linarith only [h2, h9, hc34, hlam, hphi, u4elo0]
                · linarith only [h0, h6, h8, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                  · rcases h5bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [hlam, p40_0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p40_1, u1elo0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h2, h7, hc23, hlam, hphi, ht34, p40_1, u4elo0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h2, h7, hc23, hlam, hphi, ht34, p40_1, u4elo0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p40_1, u4elo0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h1, hlam, p40_0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [hlam, p40_0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h0, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40_1, u1elo0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h0, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40_1, u1elo0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h0, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p40_1, u1elo0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1, u2elo4]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h4, hlam, p40_1]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [hlam, p40_0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h7, hlam, p40_1]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1, u2elo4]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h1, h5, hlam, p40_1]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h5, hlam, p40_1]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h0, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, p40_1, u1elo0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [hlam, p40_0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h0, h5, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p40_1, u1elo0]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h2, hlam, p40_1]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h6, hlam, p40_1]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h38, hlam, p40_1]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [h39, hlam, p40_1]
                    · have p40_0 := h40c.1
                      have p40_1 := h40c.2.1
                      have p40_2 := h40c.2.2.1
                      have p40_3 := h40c.2.2.2
                      linarith only [hlam, p40_0]
                  · linarith only [h2, h39, hc34, hlam, hphi, u4elo0]
                · linarith only [h0, h38, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h2, h6, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
            · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
              · linarith only [h4, h5, h70, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                · rcases m.htr 3 4 5 (by decide) (by decide) with h73 | h73
                  · rcases h5bigk with h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [hlam, p74_0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p74_1, u1elo0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h2, h70, hc23, hlam, hphi, ht34, p74_1, u4elo0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h2, h5, hc13, hlam, hphi, ht34, p74_1, u4elo0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p74_1, u4elo0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h1, hlam, p74_0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [hlam, p74_0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h70, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p74_1, u1elo4]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h5, hlam, p74_0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h69, hc45, hlam, hphi, ht01, ht0b, ht5b, p74_1, u1elo3]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p74_1, u2elo4]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h4, hlam, p74_1]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [hlam, p74_0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h70, hlam, p74_1]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h0, h4, h69, hc45, hlam, hphi, ht01, ht0b, ht5b, p74_1, u1elo0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h73, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p74_1, u4elo3]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h4, h73, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p74_1, u4elo3]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h73, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p74_1, u4elo3]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [hlam, p74_0]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h73, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p74_1, u4elo3]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h2, hlam, p74_1]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h69, hlam, p74_1]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h72, hlam, p74_1]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [h73, hlam, p74_1]
                    · have p74_0 := h74c.1
                      have p74_1 := h74c.2.1
                      have p74_2 := h74c.2.2.1
                      have p74_3 := h74c.2.2.2
                      linarith only [hlam, p74_0]
                  · linarith only [h3, h72, h73, hc34, hlam, hphi, u4elo1]
                · linarith only [h2, h72, hc24, hlam, hphi, u4elo0]
            · linarith only [h2, h69, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
          · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
            · linarith only [h104, h3, h4, hlam]
            · linarith only [h104, h2, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
            · linarith only [h107, h3, h4, hlam]
            · linarith only [h107, h2, hc14, hlam, hphi, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
        · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
          · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
            · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
              · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                  · rcases h5bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [hlam, p116_0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p116_1, u1elo0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h113, h115, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p116_1, u4elo0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h115, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p116_1, u4elo0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p116_1, u4elo0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h1, hlam, p116_0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [hlam, p116_0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h113, h115, hc45, hlam, hphi, ht01, ht0b, ht5b, p116_1, u1elo4]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h110, h115, hc45, hlam, hphi, ht01, ht0b, ht5b, p116_1, u1elo1]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h110, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p116_1, u4elo2]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p116_1, u2elo4]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h110, hlam, p116_1]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [hlam, p116_0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h115, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p116_1, u2elo4]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h110, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p116_1, u4elo2]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h113, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p116_1, u2elo2]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h111, hlam, p116_1]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h113, hlam, p116_0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [hlam, p116_0]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h111, hc45, hlam, hphi, ht01, ht0b, ht5b, p116_1, u1elo2]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h2, hlam, p116_1]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h112, hlam, p116_1]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h114, hlam, p116_1]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [h115, hlam, p116_1]
                    · have p116_0 := h116c.1
                      have p116_1 := h116c.2.1
                      have p116_2 := h116c.2.2.1
                      have p116_3 := h116c.2.2.2
                      linarith only [hlam, p116_0]
                  · linarith only [h115, h2, hc34, hlam, hphi, u4elo0]
                · linarith only [h0, h112, h114, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · linarith only [h110, h111, h113, h3, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h112, h2, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h146 | h146
            · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
              · linarith only [h110, h111, h147, h3, hc13, hlam, hphi, ht34, u4elo2]
              · linarith only [h110, h147, h3, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h110, h146, h2, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
          · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
            · rcases m.htr 2 3 5 (by decide) (by decide) with h153 | h153
              · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                · rcases m.htr 3 4 5 (by decide) (by decide) with h155 | h155
                  · rcases h5bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [hlam, p156_0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h1, h110, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p156_1, u1elo0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h110, h2, hc12, hlam, hphi, ht23, ht34, p156_1, u4elo0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p156_1, u4elo0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p156_1, u4elo0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h1, hlam, p156_0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [hlam, p156_0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h110, hlam, p156_0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h155, hc45, hlam, hphi, ht01, ht0b, ht5b, p156_1, u1elo4]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h0, h152, hc45, hlam, hphi, ht01, ht0b, ht5b, p156_1, u1elo0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h154, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p156_1, u4elo2]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h154, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p156_1, u4elo2]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [hlam, p156_0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h154, h155, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p156_1, u4elo2]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h154, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p156_1, u4elo2]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h1, h110, hc12, hc35, hlam, hphi, ht23, p156_1]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h151, hlam, p156_1]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h153, hlam, p156_0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [hlam, p156_0]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h151, hc45, hlam, hphi, ht01, ht0b, ht5b, p156_1, u1elo4]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h2, hlam, p156_1]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h152, hlam, p156_1]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h154, hlam, p156_1]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [h155, hlam, p156_1]
                    · have p156_0 := h156c.1
                      have p156_1 := h156c.2.1
                      have p156_2 := h156c.2.2.1
                      have p156_3 := h156c.2.2.2
                      linarith only [hlam, p156_0]
                  · linarith only [h155, h2, hc34, hlam, hphi, u4elo0]
                · linarith only [h0, h152, h154, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h110, h151, h153, hlam]
            · linarith only [h152, h2, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h186 | h186
            · rcases m.htr 2 3 5 (by decide) (by decide) with h187 | h187
              · rcases m.htr 2 4 5 (by decide) (by decide) with h188 | h188
                · rcases m.htr 3 4 5 (by decide) (by decide) with h189 | h189
                  · rcases h5bigk with h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [hlam, p190_0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p190_1, u1elo0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h110, h2, hc12, hlam, hphi, ht23, ht34, p190_1, u4elo0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p190_1, u4elo0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p190_1, u4elo0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h1, hlam, p190_0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [hlam, p190_0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h110, hlam, p190_0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h151, hlam, p190_0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p190_1, u1elo4]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h188, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u2elo3]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h188, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p190_1, u4elo2]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [hlam, p190_0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h188, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p190_1, u4elo2]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h188, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p190_1, u4elo2]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h1, h110, h189, hc12, hc34, hlam, hphi, ht23, p190_1]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h110, h189, hc12, hlam, hphi, ht23, ht34, p190_1, u4elo3]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h187, hlam, p190_0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [hlam, p190_0]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h187, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u2elo2]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h2, hlam, p190_1]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h186, hlam, p190_1]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h188, hlam, p190_1]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [h189, hlam, p190_1]
                    · have p190_0 := h190c.1
                      have p190_1 := h190c.2.1
                      have p190_2 := h190c.2.2.1
                      have p190_3 := h190c.2.2.2
                      linarith only [hlam, p190_0]
                  · linarith only [h186, h189, hc34, hlam, hphi, u4elo1]
                · linarith only [h0, h186, h188, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h218 | h218
                · rcases m.htr 3 4 5 (by decide) (by decide) with h219 | h219
                  · rcases h5bigk with h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h1, h110, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p220_1, u1elo0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h110, h2, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p220_1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h110, h187, h2, hc12, hlam, hphi, ht23, ht34, p220_1, u4elo0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p220_1, u4elo0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h1, hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h110, hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h151, hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p220_1, u1elo4]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p220_1, u2elo4]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h187, h219, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p220_1, u4elo3]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h187, hlam, p220_1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h187, h219, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p220_1, u4elo3]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h1, h110, h219, hc12, hlam, hphi, ht23, ht34, p220_1, u4elo3]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h110, h219, hc12, hlam, hphi, ht23, ht34, p220_1, u4elo3]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h219, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p220_1, u4elo3]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h219, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p220_1, u4elo3]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h2, hlam, p220_1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h186, hlam, p220_1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h218, hlam, p220_1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h219, hlam, p220_1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                  · linarith only [h2, h219, hc34, hlam, hphi, u4elo0]
                · linarith only [h186, h218, h3, hlam]
            · linarith only [h186, h2, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h249 | h249
      · rcases m.htr 1 2 5 (by decide) (by decide) with h250 | h250
        · rcases m.htr 1 3 5 (by decide) (by decide) with h251 | h251
          · rcases m.htr 1 4 5 (by decide) (by decide) with h252 | h252
            · linarith only [h2, h252, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h254 | h254
              · rcases m.htr 2 4 5 (by decide) (by decide) with h255 | h255
                · linarith only [h0, h2, h249, h255, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h257 | h257
                  · linarith only [h0, h2, h249, h257, hc24, hlam, hphi, u4elo3]
                  · rcases h5bigk with h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p259_1, u1elo0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h2, h254, h257, hc34, hlam, hphi, p259_1, u4elo4]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h2, h257, hc34, hlam, hphi, p259_1, u4elo4]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h2, hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h1, hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h254, h257, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p259_1, u1elo4]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h1, h257, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p259_1, u1elo0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h252, hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p259_1, u2elo4]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h250, hlam, p259_1]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h250, h257, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p259_1, u2elo1]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h255, hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h251, hc05, hlam, hphi, ht01, ht0b, ht5b, p259_1, u1elo2]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h251, hlam, p259_1]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h254, hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h257, hlam, p259_0]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h1, h250, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p259_1, u4elo4]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [h250, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p259_1, u4elo4]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p259_1, u4elo4]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p259_1, u4elo4]
                    · have p259_0 := h259c.1
                      have p259_1 := h259c.2.1
                      have p259_2 := h259c.2.2.1
                      have p259_3 := h259c.2.2.2
                      linarith only [hlam, p259_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h285 | h285
                · linarith only [h0, h2, h249, h285, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h287 | h287
                  · linarith only [h2, h287, hc04, hlam, hphi, u4elo3]
                  · rcases h5bigk with h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h251, h254, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h2, h254, hc23, hlam, hphi, ht34, p289_1, u4elo4]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h2, h254, hc23, hlam, hphi, ht34, p289_1, u4elo4]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h2, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h1, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h254, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p289_1, u1elo4]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h1, h254, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p289_1, u1elo0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h252, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p289_1, u2elo4]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h250, hlam, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h254, hlam, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h285, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h2, h251, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p289_1, u1elo2]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h251, hlam, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h251, hc25, hlam, hphi, ht01, ht0b, ht5b, p289_1, u1elo4]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h287, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p289_1, u4elo4]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h251, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p289_1, u4elo4]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h254, hc23, hlam, hphi, ht34, p289_1, u4elo4]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h254, hc23, hlam, hphi, ht34, p289_1, u4elo4]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
            · linarith only [h0, h2, h315, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h317 | h317
              · linarith only [h250, h251, h317, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h319 | h319
                · linarith only [h2, h319, hc04, hlam, hphi, u4elo2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h321 | h321
                  · linarith only [h0, h2, h249, h321, hc24, hlam, hphi, u4elo3]
                  · rcases h5bigk with h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p323_1, u1elo0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h2, h317, hc23, hlam, hphi, ht34, p323_1, u4elo4]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h2, h251, hc13, hlam, hphi, ht34, p323_1, u4elo4]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h2, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h1, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h317, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p323_1, u1elo4]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h251, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h315, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p323_1, u2elo4]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h250, hlam, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h317, hlam, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h319, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h1, h251, hc13, hc35, hlam, hphi, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h251, hc13, hc35, hlam, hphi, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h317, hc23, hc35, hlam, hphi, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h321, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h0, h2, h249, hc24, hlam, hphi, p323_1, u4elo4]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h251, hc13, hlam, hphi, ht34, p323_1, u4elo4]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h317, hc23, hlam, hphi, ht34, p323_1, u4elo4]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p323_1, u4elo4]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h349 | h349
          · rcases m.htr 1 4 5 (by decide) (by decide) with h350 | h350
            · linarith only [h0, h2, h350, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h352 | h352
              · rcases m.htr 2 4 5 (by decide) (by decide) with h353 | h353
                · linarith only [h2, h249, h353, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · linarith only [h249, h250, h353, hc24, hlam, hphi, u4elo4]
              · linarith only [h249, h250, h349, h352, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h357 | h357
            · linarith only [h0, h2, h357, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h359 | h359
              · rcases m.htr 2 4 5 (by decide) (by decide) with h360 | h360
                · linarith only [h2, h249, h250, h349, h359, h360, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h249, h250, h360, hc24, hlam, hphi, u4elo4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h363 | h363
                · linarith only [h249, h250, h363, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                · linarith only [h249, h250, h363, hc24, hlam, hphi, u4elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h366 | h366
        · rcases m.htr 1 3 5 (by decide) (by decide) with h367 | h367
          · rcases m.htr 1 4 5 (by decide) (by decide) with h368 | h368
            · linarith only [h0, h2, h368, hlam]
            · linarith only [h249, h366, h368, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h371 | h371
            · linarith only [h0, h2, h371, hlam]
            · linarith only [h249, h366, h371, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
          · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
            · linarith only [h0, h2, h375, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
              · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                · linarith only [h0, h2, h249, h378, hc12, hlam, hphi, u2elo3]
                · linarith only [h249, h378, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · linarith only [h366, h374, h377, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h382 | h382
            · linarith only [h0, h2, h382, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h384 | h384
              · rcases m.htr 2 4 5 (by decide) (by decide) with h385 | h385
                · linarith only [h0, h2, h385, hc14, hlam, hphi, u4elo2]
                · linarith only [h249, h385, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h388 | h388
                · linarith only [h0, h2, h249, h388, hc12, hlam, hphi, ht23, ht34, u4elo2]
                · linarith only [h249, h388, hc12, hlam, hphi, ht23, ht34, u4elo4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h391 | h391
    · linarith only [h0, h1, h391, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h393 | h393
      · rcases m.htr 1 2 5 (by decide) (by decide) with h394 | h394
        · rcases m.htr 1 3 5 (by decide) (by decide) with h395 | h395
          · rcases m.htr 1 4 5 (by decide) (by decide) with h396 | h396
            · linarith only [h0, h1, h391, h394, h396, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · linarith only [h0, h1, h396, hc14, hlam, hphi, u4elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
            · linarith only [h0, h1, h394, h399, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
            · linarith only [h0, h1, h393, h399, hc24, hlam, hphi, u4elo4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h402 | h402
          · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
            · linarith only [h0, h1, h403, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
            · linarith only [h0, h1, h403, hc14, hlam, hphi, u4elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h406 | h406
            · linarith only [h0, h1, h394, h406, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
            · linarith only [h0, h1, h393, h406, hc24, hlam, hphi, u4elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
        · linarith only [h0, h1, h393, h409, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
        · linarith only [h0, h1, h393, h409, hc12, hlam, hphi, u2elo4]

end R2N4
