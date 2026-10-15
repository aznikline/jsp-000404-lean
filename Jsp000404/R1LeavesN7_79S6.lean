import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_I_L_0_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
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
                    linarith only [hc15, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc25, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc35, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc45, hlam, hphi, p8_1, u5elo0]
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
                    linarith only [hc25, hlam, hphi, p8_1, u5elo1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, hc35, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, hc45, hlam, hphi, p8_1, u5elo0]
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
                    linarith only [h7, hc45, hlam, hphi, p8_1, u5elo2]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u2elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc05, hlam, hphi, p8_1, u5elo3]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h4, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h4, hc25, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h4, hc45, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h2, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h5, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h6, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h7, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                · linarith only [h2, h7, hc34, hlam, hphi, u4elo0]
              · linarith only [h2, h6, hc24, hlam, hphi, u4elo0]
            · linarith only [h2, h5, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
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
                    linarith only [hc15, hlam, hphi, p40_1, u5elo0]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hc25, hlam, hphi, p40_1, u5elo0]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h4, hc15, hlam, hphi, p40_1, u5elo0]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hc45, hlam, hphi, p40_1, u5elo0]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h0, hlam, p40_0]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hlam, p40_0]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hc25, hlam, hphi, p40_1, u5elo1]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h4, hlam, p40_0]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h4, hc45, hlam, hphi, p40_1, u5elo3]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h1, hlam, p40_1]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h3, hlam, p40_1]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hlam, p40_0]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h4, hc15, hlam, hphi, p40_1, u5elo2]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hc45, hlam, hphi, p40_1, u5elo2]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hc05, hlam, hphi, p40_1, u5elo3]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h39, h4, hc13, hlam, hphi, ht34, p40_1, u4elo3]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hc25, hlam, hphi, p40_1, u5elo3]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hlam, p40_0]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [hc45, hlam, hphi, p40_1, u5elo3]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h2, hlam, p40_1]
                  · have p40_0 := h40c.1
                    have p40_1 := h40c.2.1
                    have p40_2 := h40c.2.2.1
                    have p40_3 := h40c.2.2.2
                    linarith only [h37, hlam, p40_1]
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
                · linarith only [h37, h39, hc34, hlam, hphi, u4elo1]
              · linarith only [h37, h38, hc24, hlam, hphi, u4elo1]
            · linarith only [h2, h37, hc14, hlam, hphi, u4elo0]
        · linarith only [h1, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
        · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
          · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
            · linarith only [h2, h72, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
              · linarith only [h2, h74, hc04, hlam, hphi, u4elo2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                · linarith only [h2, h76, hc04, hlam, hphi, u4elo3]
                · rcases h5bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc15, hlam, hphi, p78_1, u5elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc25, hlam, hphi, p78_1, u5elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc35, hlam, hphi, p78_1, u5elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h2, hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h0, hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h74, hc24, hlam, hphi, ht45, p78_1, u5elo1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h0, h2, hc35, hlam, hphi, p78_1, u5elo4]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h72, hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h1, hlam, p78_1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h70, hlam, p78_1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h76, hc34, hlam, hphi, ht45, p78_1, u5elo2]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h74, hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc05, hlam, hphi, p78_1, u5elo3]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h71, hlam, p78_1]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h0, h71, hc25, hlam, hphi, p78_1, u5elo0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h76, hlam, p78_0]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc05, hlam, hphi, p78_1, u5elo4]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [h71, hc35, hlam, hphi, p78_1, u5elo4]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc25, hlam, hphi, p78_1, u5elo4]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hc35, hlam, hphi, p78_1, u5elo4]
                  · have p78_0 := h78c.1
                    have p78_1 := h78c.2.1
                    have p78_2 := h78c.2.2.1
                    have p78_3 := h78c.2.2.2
                    linarith only [hlam, p78_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
            · linarith only [h104, h2, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
              · linarith only [h106, h2, hc04, hlam, hphi, u4elo2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                · linarith only [h108, h2, hc04, hlam, hphi, u4elo3]
                · rcases h5bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h104, hc14, hlam, hphi, ht45, p110_1, u5elo0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h106, hc24, hlam, hphi, ht45, p110_1, u5elo0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h2, h71, hc13, hlam, hphi, ht34, p110_1, u4elo4]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h2, hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h0, hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h106, hc24, hlam, hphi, ht45, p110_1, u5elo1]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h71, hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h104, hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h1, hlam, p110_1]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h70, hlam, p110_1]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h71, hc15, hlam, hphi, p110_1, u5elo2]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h106, hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h0, h70, hc25, hlam, hphi, p110_1, u5elo3]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h70, hc25, hlam, hphi, p110_1, u5elo3]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h106, h108, hc24, hlam, hphi, ht45, p110_1, u5elo4]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h108, hlam, p110_0]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h0, h71, hc13, hlam, hphi, ht34, ht45, p110_1, u5elo4]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h71, hc13, hlam, hphi, ht34, ht45, p110_1, u5elo4]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [h106, hc24, hlam, hphi, ht45, p110_1, u5elo4]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [hc35, hlam, hphi, p110_1, u5elo4]
                  · have p110_0 := h110c.1
                    have p110_1 := h110c.2.1
                    have p110_2 := h110c.2.2.1
                    have p110_3 := h110c.2.2.2
                    linarith only [hlam, p110_0]
        · linarith only [h1, h70, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
      · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
        · linarith only [h1, h138, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
          · rcases m.htr 1 4 5 (by decide) (by decide) with h141 | h141
            · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
              · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
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
                    linarith only [h138, hc12, hlam, hphi, ht23, ht34, ht45, p144_1, u5elo0]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h1, hlam, p144_0]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h143, hc45, hlam, hphi, p144_1, u5elo0]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h1, hc45, hlam, hphi, p144_1, u5elo2]
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
                    linarith only [h138, hlam, p144_0]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h143, hc45, hlam, hphi, p144_1, u5elo1]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h0, h1, hc45, hlam, hphi, p144_1, u5elo2]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [hc05, hlam, hphi, p144_1, u5elo2]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [hc15, hlam, hphi, p144_1, u5elo2]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [hlam, p144_0]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h143, hc45, hlam, hphi, p144_1, u5elo2]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [hc45, hlam, hphi, p144_1, u5elo2]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h0, h138, hc12, hlam, hphi, ht23, ht34, ht45, p144_1, u5elo3]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h140, hlam, p144_1]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h0, h140, hc25, hlam, hphi, p144_1, u5elo0]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [hlam, p144_0]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h0, h140, hc45, hlam, hphi, p144_1, u5elo0]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h137, hlam, p144_1]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h141, hlam, p144_1]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h142, hlam, p144_1]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [h143, hlam, p144_1]
                  · have p144_0 := h144c.1
                    have p144_1 := h144c.2.1
                    have p144_2 := h144c.2.2.1
                    have p144_3 := h144c.2.2.2
                    linarith only [hlam, p144_0]
                · linarith only [h137, h143, hc34, hlam, hphi, u4elo0]
              · linarith only [h137, h142, hc24, hlam, hphi, u4elo0]
            · linarith only [h137, h141, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
            · rcases m.htr 2 4 5 (by decide) (by decide) with h174 | h174
              · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                · rcases h5bigk with h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hlam, p176_0]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h1, hc15, hlam, hphi, p176_1, u5elo2]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h1, hlam, p176_0]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h1, h140, hc13, hlam, hphi, ht34, ht45, p176_1, u5elo2]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h1, hc45, hlam, hphi, p176_1, u5elo2]
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
                    linarith only [h138, hlam, p176_0]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h140, hlam, p176_0]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hc45, hlam, hphi, p176_1, u5elo1]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hc05, hlam, hphi, p176_1, u5elo2]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hc15, hlam, hphi, p176_1, u5elo2]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hlam, p176_0]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h140, hc13, hlam, hphi, ht34, ht45, p176_1, u5elo2]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hc45, hlam, hphi, p176_1, u5elo2]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hc05, hlam, hphi, p176_1, u5elo3]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h138, hc12, hlam, hphi, ht23, ht34, ht45, p176_1, u5elo3]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hc25, hlam, hphi, p176_1, u5elo3]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hlam, p176_0]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hc45, hlam, hphi, p176_1, u5elo3]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h137, hlam, p176_1]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h173, hlam, p176_1]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h174, hlam, p176_1]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [h175, hlam, p176_1]
                  · have p176_0 := h176c.1
                    have p176_1 := h176c.2.1
                    have p176_2 := h176c.2.2.1
                    have p176_3 := h176c.2.2.2
                    linarith only [hlam, p176_0]
                · linarith only [h173, h175, hc34, hlam, hphi, u4elo1]
              · linarith only [h137, h174, hc24, hlam, hphi, u4elo0]
            · linarith only [h137, h173, hc14, hlam, hphi, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h205 | h205
        · linarith only [h1, h205, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h207 | h207
          · rcases m.htr 1 4 5 (by decide) (by decide) with h208 | h208
            · linarith only [h137, h208, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h210 | h210
              · linarith only [h208, h210, hc14, hlam, hphi, u4elo2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h212 | h212
                · linarith only [h1, h210, h212, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · rcases h5bigk with h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hc15, hlam, hphi, p214_1, u5elo0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h1, hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h1, h210, h212, hc34, hlam, hphi, p214_1, u4elo4]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h137, hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h0, hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h205, hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h212, hc34, hlam, hphi, ht45, p214_1, u5elo1]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h208, hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h210, hc05, hlam, hphi, p214_1, u5elo4]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h210, hc15, hlam, hphi, p214_1, u5elo4]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h210, h212, hc34, hlam, hphi, ht45, p214_1, u5elo4]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h210, hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hc05, hlam, hphi, p214_1, u5elo3]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h207, hlam, p214_1]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h1, h207, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p214_1]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h212, hlam, p214_0]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hc05, hlam, hphi, p214_1, u5elo4]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [h205, hc12, hlam, hphi, ht23, ht34, ht45, p214_1, u5elo4]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hc25, hlam, hphi, p214_1, u5elo4]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hc35, hlam, hphi, p214_1, u5elo4]
                  · have p214_0 := h214c.1
                    have p214_1 := h214c.2.1
                    have p214_2 := h214c.2.2.1
                    have p214_3 := h214c.2.2.2
                    linarith only [hlam, p214_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h240 | h240
            · linarith only [h137, h240, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
              · linarith only [h137, h242, hc04, hlam, hphi, u4elo2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h244 | h244
                · linarith only [h1, h242, h244, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · rcases h5bigk with h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h205, hc12, hlam, hphi, ht23, ht34, ht45, p246_1, u5elo0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h1, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h1, h207, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p246_1, u2elo4]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h137, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h0, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h205, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h207, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h240, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hc05, hlam, hphi, p246_1, u5elo2]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h240, h242, hc14, hlam, hphi, ht45, p246_1, u5elo4]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h207, h242, hc13, hlam, hphi, ht34, ht45, p246_1, u5elo4]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h242, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h0, h205, hc12, hlam, hphi, ht23, ht34, ht45, p246_1, u5elo3]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h205, hc12, hlam, hphi, ht23, ht34, ht45, p246_1, u5elo3]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h244, hc25, hlam, hphi, p246_1, u5elo4]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h244, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h0, h205, hc12, hlam, hphi, ht23, ht34, ht45, p246_1, u5elo4]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h205, hc12, hlam, hphi, ht23, ht34, ht45, p246_1, u5elo4]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p246_1, u5elo4]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hc35, hlam, hphi, p246_1, u5elo4]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h272 | h272
    · rcases m.htr 0 4 5 (by decide) (by decide) with h273 | h273
      · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
        · rcases m.htr 1 3 5 (by decide) (by decide) with h275 | h275
          · rcases m.htr 1 4 5 (by decide) (by decide) with h276 | h276
            · rcases m.htr 2 4 5 (by decide) (by decide) with h277 | h277
              · rcases m.htr 3 4 5 (by decide) (by decide) with h278 | h278
                · rcases h5bigk with h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h0, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h277, hc45, hlam, hphi, p279_1, u5elo0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h278, hc45, hlam, hphi, p279_1, u5elo0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h0, hc45, hlam, hphi, p279_1, u5elo1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hc05, hlam, hphi, p279_1, u5elo1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h277, hc45, hlam, hphi, p279_1, u5elo1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h278, hc45, hlam, hphi, p279_1, u5elo1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hc45, hlam, hphi, p279_1, u5elo1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h272, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h274, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h272, h278, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p279_1, u2elo0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h272, hc45, hlam, hphi, p279_1, u5elo0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hc05, hlam, hphi, p279_1, u5elo3]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h275, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h275, hc25, hlam, hphi, p279_1, u5elo1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h275, hc45, hlam, hphi, p279_1, u5elo1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h273, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h276, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h277, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h278, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                · linarith only [h273, h278, hc34, hlam, hphi, u4elo0]
              · linarith only [h273, h277, hc24, hlam, hphi, u4elo0]
            · linarith only [h273, h276, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
            · rcases m.htr 2 4 5 (by decide) (by decide) with h309 | h309
              · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                · rcases h5bigk with h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [hlam, p311_0]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h0, hlam, p311_1]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [hc25, hlam, hphi, p311_1, u5elo0]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h0, h275, hlam, p311_1]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h0, h275, hc45, hlam, hphi, p311_1, u5elo3]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h275, hc05, hlam, hphi, p311_1, u5elo3]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [hlam, p311_0]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h275, hc25, hlam, hphi, p311_1, u5elo3]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h275, hlam, p311_0]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h275, hc45, hlam, hphi, p311_1, u5elo3]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h272, hlam, p311_1]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h274, hlam, p311_1]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [hlam, p311_0]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h275, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p311_1, u2elo4]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h272, hc45, hlam, hphi, p311_1, u5elo0]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h272, hc25, hlam, hphi, p311_1, u5elo3]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p311_1, u5elo3]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [hc25, hlam, hphi, p311_1, u5elo3]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [hlam, p311_0]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [hc45, hlam, hphi, p311_1, u5elo3]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h273, hlam, p311_1]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h308, hlam, p311_1]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h309, hlam, p311_1]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [h310, hlam, p311_1]
                  · have p311_0 := h311c.1
                    have p311_1 := h311c.2.1
                    have p311_2 := h311c.2.2.1
                    have p311_3 := h311c.2.2.2
                    linarith only [hlam, p311_0]
                · linarith only [h309, h310, hc34, hlam, hphi, u4elo2]
              · linarith only [h273, h309, hc24, hlam, hphi, u4elo0]
            · linarith only [h273, h308, hc14, hlam, hphi, u4elo0]
        · linarith only [h272, h274, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h341 | h341
        · rcases m.htr 1 3 5 (by decide) (by decide) with h342 | h342
          · rcases m.htr 1 4 5 (by decide) (by decide) with h343 | h343
            · linarith only [h273, h343, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h345 | h345
              · linarith only [h343, h345, hc14, hlam, hphi, u4elo2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h347 | h347
                · linarith only [h0, h343, h347, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · rcases h5bigk with h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [hlam, p349_0]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h0, hlam, p349_1]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [hc25, hlam, hphi, p349_1, u5elo0]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h0, h343, hc35, hlam, hphi, p349_1, u5elo4]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h273, hlam, p349_0]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h343, hc05, hlam, hphi, p349_1, u5elo4]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [hlam, p349_0]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h343, h345, hc24, hlam, hphi, ht45, p349_1, u5elo4]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h343, hc35, hlam, hphi, p349_1, u5elo4]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h343, hlam, p349_0]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h272, hlam, p349_1]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h341, hlam, p349_1]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [hlam, p349_0]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h347, hc34, hlam, hphi, ht45, p349_1, u5elo2]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h345, hlam, p349_0]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p349_1, u5elo3]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h342, hlam, p349_1]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h342, h343, h345, hc24, hlam, hphi, ht45, p349_1, u5elo4]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [hlam, p349_0]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h347, hlam, p349_0]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p349_1, u5elo4]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [hc15, hlam, hphi, p349_1, u5elo4]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [h345, hc24, hlam, hphi, ht45, p349_1, u5elo4]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [hc35, hlam, hphi, p349_1, u5elo4]
                  · have p349_0 := h349c.1
                    have p349_1 := h349c.2.1
                    have p349_2 := h349c.2.2.1
                    have p349_3 := h349c.2.2.2
                    linarith only [hlam, p349_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
            · linarith only [h273, h375, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h377 | h377
              · linarith only [h0, h375, h377, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
                · linarith only [h0, h375, h379, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · rcases h5bigk with h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, hlam, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h377, hc24, hlam, hphi, ht45, p381_1, u5elo0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h342, hlam, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h273, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hc05, hlam, hphi, p381_1, u5elo1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h342, h377, h379, hc24, hlam, hphi, ht45, p381_1, u5elo4]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h342, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h375, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h272, hlam, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h341, hlam, p381_1]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h342, hc01, hlam, hphi, ht12, p381_1, u2elo4]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h377, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h379, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p381_1, u5elo4]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, h379, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p381_1, u5elo4]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h379, hc25, hlam, hphi, p381_1, u5elo4]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h379, hlam, p381_0]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p381_1, u5elo4]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p381_1, u5elo4]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hc25, hlam, hphi, p381_1, u5elo4]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hc35, hlam, hphi, p381_1, u5elo4]
                  · have p381_0 := h381c.1
                    have p381_1 := h381c.2.1
                    have p381_2 := h381c.2.2.1
                    have p381_3 := h381c.2.2.2
                    linarith only [hlam, p381_0]
        · linarith only [h272, h341, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
      · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
        · linarith only [h272, h409, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
          · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
            · rcases m.htr 2 4 5 (by decide) (by decide) with h413 | h413
              · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                · rcases h5bigk with h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [hlam, p415_0]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h0, hlam, p415_1]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h272, hlam, p415_0]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h414, hc45, hlam, hphi, p415_1, u5elo0]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [hc45, hlam, hphi, p415_1, u5elo0]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [hc05, hlam, hphi, p415_1, u5elo1]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [hlam, p415_0]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h409, hlam, p415_0]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h409, h414, hc45, hlam, hphi, p415_1, u5elo2]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h409, hc45, hlam, hphi, p415_1, u5elo2]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p415_1, u5elo2]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [hc15, hlam, hphi, p415_1, u5elo2]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [hlam, p415_0]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h414, hc45, hlam, hphi, p415_1, u5elo2]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [hc45, hlam, hphi, p415_1, u5elo2]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p415_1, u5elo3]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h411, hlam, p415_1]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h409, h414, hc12, hc34, hlam, hphi, ht23, p415_1]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [hlam, p415_0]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h409, h411, hc45, hlam, hphi, p415_1, u5elo2]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h408, hlam, p415_1]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h412, hlam, p415_1]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h413, hlam, p415_1]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [h414, hlam, p415_1]
                  · have p415_0 := h415c.1
                    have p415_1 := h415c.2.1
                    have p415_2 := h415c.2.2.1
                    have p415_3 := h415c.2.2.2
                    linarith only [hlam, p415_0]
                · linarith only [h408, h414, hc34, hlam, hphi, u4elo0]
              · linarith only [h408, h413, hc24, hlam, hphi, u4elo0]
            · linarith only [h408, h412, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h444 | h444
            · rcases m.htr 2 4 5 (by decide) (by decide) with h445 | h445
              · rcases m.htr 3 4 5 (by decide) (by decide) with h446 | h446
                · rcases h5bigk with h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hlam, p447_0]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h0, hlam, p447_1]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h272, hlam, p447_0]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h411, hc13, hlam, hphi, ht34, ht45, p447_1, u5elo0]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hc45, hlam, hphi, p447_1, u5elo0]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hc05, hlam, hphi, p447_1, u5elo1]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hlam, p447_0]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h409, hlam, p447_0]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h411, hlam, p447_0]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h409, hc45, hlam, hphi, p447_1, u5elo2]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p447_1, u5elo2]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hc15, hlam, hphi, p447_1, u5elo2]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hlam, p447_0]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hc35, hlam, hphi, p447_1, u5elo2]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hc45, hlam, hphi, p447_1, u5elo2]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h0, h446, hc01, hlam, hphi, ht12, ht23, ht34, p447_1, u4elo3]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h0, h446, hc01, hc34, hlam, hphi, ht12, ht23, p447_1]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hc25, hlam, hphi, p447_1, u5elo3]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hlam, p447_0]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hc45, hlam, hphi, p447_1, u5elo3]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h408, hlam, p447_1]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h444, hlam, p447_1]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h445, hlam, p447_1]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [h446, hlam, p447_1]
                  · have p447_0 := h447c.1
                    have p447_1 := h447c.2.1
                    have p447_2 := h447c.2.2.1
                    have p447_3 := h447c.2.2.2
                    linarith only [hlam, p447_0]
                · linarith only [h408, h446, hc34, hlam, hphi, u4elo0]
              · linarith only [h408, h445, hc24, hlam, hphi, u4elo0]
            · linarith only [h408, h444, hc14, hlam, hphi, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h476 | h476
        · linarith only [h272, h476, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h478 | h478
          · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
            · linarith only [h408, h479, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h481 | h481
              · linarith only [h0, h479, h481, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h483 | h483
                · linarith only [h0, h476, h481, h483, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · rcases h5bigk with h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h0, hlam, p485_1]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h272, hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hc35, hlam, hphi, p485_1, u5elo0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h408, hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hc05, hlam, hphi, p485_1, u5elo1]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h476, hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h476, h481, hc35, hlam, hphi, p485_1, u5elo4]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h479, hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h0, h481, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p485_1, u5elo4]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h481, hc15, hlam, hphi, p485_1, u5elo4]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h481, h483, hc34, hlam, hphi, ht45, p485_1, u5elo4]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h481, hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p485_1, u5elo3]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h478, hlam, p485_1]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h476, h478, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p485_1]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h483, hlam, p485_0]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p485_1, u5elo4]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hc15, hlam, hphi, p485_1, u5elo4]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hc25, hlam, hphi, p485_1, u5elo4]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hc35, hlam, hphi, p485_1, u5elo4]
                  · have p485_0 := h485c.1
                    have p485_1 := h485c.2.1
                    have p485_2 := h485c.2.2.1
                    have p485_3 := h485c.2.2.2
                    linarith only [hlam, p485_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h511 | h511
            · linarith only [h408, h511, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h513 | h513
              · linarith only [h0, h511, h513, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h515 | h515
                · linarith only [h0, h476, h513, h515, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · rcases h5bigk with h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h0, hlam, p517_1]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h272, hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h0, h478, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p517_1, u5elo0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h408, hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [hc05, hlam, hphi, p517_1, u5elo1]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h476, hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h478, hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h511, hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h0, h513, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p517_1, u5elo4]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h513, hc15, hlam, hphi, p517_1, u5elo4]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h0, h478, h513, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p517_1, u5elo4]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h513, hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p517_1, u5elo3]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p517_1]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h515, hc25, hlam, hphi, p517_1, u5elo4]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h515, hlam, p517_0]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p517_1, u5elo4]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p517_1, u5elo4]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [h0, h476, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p517_1, u5elo4]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [hc35, hlam, hphi, p517_1, u5elo4]
                  · have p517_0 := h517c.1
                    have p517_1 := h517c.2.1
                    have p517_2 := h517c.2.2.1
                    have p517_3 := h517c.2.2.2
                    linarith only [hlam, p517_0]

end R2N4
