import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_I_M_LI_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h1, h10, h13, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · linarith only [h1, h10, h12, h13, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                          · linarith only [h1, h12, h16, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases h5bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hc15, hlam, hphi, p18_1, u5elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hc25, hlam, hphi, p18_1, u5elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hc35, hlam, hphi, p18_1, u5elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h10, h12, hc34, hlam, hphi, ht45, p18_1, u5elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h0, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hc25, hlam, hphi, p18_1, u5elo1]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h0, h16, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1, u0elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h0, h10, h12, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1, u0elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h3, hlam, p18_1]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h8, hlam, p18_1]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h16, hc34, hlam, hphi, ht45, p18_1, u5elo2]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h12, hlam, p18_1]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h5, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hc15, hlam, hphi, p18_1, u5elo3]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h11, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h16, hlam, p18_1]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h6, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h9, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h1, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p18_1, u2elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h1, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p18_1, u2elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                      · linarith only [h1, h10, h11, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                      · linarith only [h1, h10, h4, h45, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                          · rcases h5bigk with h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [hc15, hlam, hphi, p49_1, u5elo0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h45, hc23, hlam, hphi, ht34, ht45, p49_1, u5elo0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [hc35, hlam, hphi, p49_1, u5elo0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [hc45, hlam, hphi, p49_1, u5elo0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h0, hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h45, hc23, hlam, hphi, ht34, ht45, p49_1, u5elo1]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h0, h45, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1, u0elo0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p49_1, u0elo0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h3, hlam, p49_1]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h8, hlam, p49_1]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h45, hlam, p49_1]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [hc45, hlam, hphi, p49_1, u5elo2]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h5, hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h1, h4, h48, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p49_1, u2elo0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h1, h4, h48, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p49_1, u2elo0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h1, h4, h48, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p49_1, u2elo0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h6, hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h9, hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h47, hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [h48, hlam, p49_0]
                            · have p49_0 := h49c.1
                              have p49_1 := h49c.2.1
                              have p49_2 := h49c.2.2.1
                              have p49_3 := h49c.2.2.2
                              linarith only [hlam, p49_0]
                          · linarith only [h1, h10, h4, h48, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                          · linarith only [h1, h10, h4, h47, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · linarith only [h10, h76, h9, hc23, hlam, hphi, ht34, ht45, u5elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                        · linarith only [h2, h81, h9, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h83 | h83
                          · linarith only [h79, h81, h83, h9, hc14, hlam, hphi, ht45, u5elo2]
                          · rcases h5bigk with h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [hlam, p85_0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [hc15, hlam, hphi, p85_1, u5elo0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h79, h81, hc34, hlam, hphi, ht45, p85_1, u5elo0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [hc35, hlam, hphi, p85_1, u5elo0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h7, h79, h9, hc34, hlam, hphi, ht45, p85_1, u5elo0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h0, hlam, p85_0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [hlam, p85_0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h79, h81, hc34, hlam, hphi, ht45, p85_1, u5elo1]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h83, hc34, hlam, hphi, ht45, p85_1, u5elo1]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h9, hlam, p85_1]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h3, hlam, p85_1]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h8, hlam, p85_1]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [hlam, p85_0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h83, hc34, hlam, hphi, ht45, p85_1, u5elo2]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h81, hlam, p85_1]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h5, hlam, p85_0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [hc15, hlam, hphi, p85_1, u5elo3]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h80, hlam, p85_0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [hlam, p85_0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h83, hlam, p85_1]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h6, hlam, p85_0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h1, h4, h6, h79, h8, h81, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p85_1, u2elo0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h1, h4, h6, h79, h81, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p85_1, u2elo0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [h1, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p85_1, u2elo0]
                            · have p85_0 := h85c.1
                              have p85_1 := h85c.2.1
                              have p85_2 := h85c.2.2.1
                              have p85_3 := h85c.2.2.2
                              linarith only [hlam, p85_0]
                      · linarith only [h1, h5, h79, h80, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h112 | h112
                      · linarith only [h1, h112, h4, h79, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                        · linarith only [h114, h7, h9, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
                          · linarith only [h1, h116, h4, h9, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · linarith only [h116, h79, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
              · linarith only [h2, h7, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h121 | h121
              · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                  · linarith only [h0, h123, h6, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                        · linarith only [h123, h127, h2, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                          · linarith only [h125, h129, h2, h6, hlam]
                          · rcases h5bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h122, hc25, hlam, hphi, p131_1, u5elo0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h6, hc25, hlam, hphi, p131_1, u5elo4]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h129, h6, hc34, hlam, hphi, ht45, p131_1, u5elo4]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h6, hlam, p131_1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h0, hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hc25, hlam, hphi, p131_1, u5elo1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h0, h129, h6, hc34, hlam, hphi, ht45, p131_1, u5elo4]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h123, hlam, p131_1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h3, hlam, p131_1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h122, hlam, p131_1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h129, hc34, hlam, hphi, ht45, p131_1, u5elo2]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h127, hlam, p131_1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h5, hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hc15, hlam, hphi, p131_1, u5elo3]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h126, hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h129, hlam, p131_1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hc05, hlam, hphi, p131_1, u5elo4]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hc15, hlam, hphi, p131_1, u5elo4]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h126, hc35, hlam, hphi, p131_1, u5elo4]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hc35, hlam, hphi, p131_1, u5elo4]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                      · linarith only [h1, h125, h126, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · linarith only [h125, h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h122, h3, hc12, hlam, hphi, u2elo0]
              · linarith only [h121, h2, hc12, hlam, hphi, u2elo0]
          · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h162 | h162
          · rcases m.htr 0 4 5 (by decide) (by decide) with h163 | h163
            · rcases m.htr 1 2 4 (by decide) (by decide) with h164 | h164
              · rcases m.htr 1 2 5 (by decide) (by decide) with h165 | h165
                · rcases m.htr 1 4 5 (by decide) (by decide) with h166 | h166
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                    · linarith only [h162, h167, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h169 | h169
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h170 | h170
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h171 | h171
                          · rcases h5bigk with h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h165, hc25, hlam, hphi, p172_1, u5elo0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hc25, hlam, hphi, p172_1, u5elo0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hc35, hlam, hphi, p172_1, u5elo0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hc45, hlam, hphi, p172_1, u5elo0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h0, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hc25, hlam, hphi, p172_1, u5elo1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h0, h171, hc45, hlam, hphi, ht0b, ht5b, p172_1, u0elo0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p172_1, u0elo0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h3, hlam, p172_1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h165, hlam, p172_1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h171, hc45, hlam, hphi, p172_1, u5elo2]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h164, h167, h169, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p172_1, u2elo1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h162, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hc15, hlam, hphi, p172_1, u5elo3]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h169, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h164, h167, h169, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p172_1, u2elo1]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h163, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h166, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h170, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [h171, hlam, p172_0]
                            · have p172_0 := h172c.1
                              have p172_1 := h172c.2.1
                              have p172_2 := h172c.2.2.1
                              have p172_3 := h172c.2.2.2
                              linarith only [hlam, p172_0]
                          · linarith only [h171, h4, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h166, h167, h169, h170, hc35, hlam, hphi, u5elo0]
                      · linarith only [h162, h169, h4, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                    · linarith only [h162, h201, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                      · linarith only [h163, h164, h166, h2, h201, h203, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h162, h203, h4, hc23, hc34, hlam, hphi]
                · linarith only [h165, h3, hc12, hlam, hphi, u2elo0]
              · linarith only [h164, h2, hc12, hlam, hphi, u2elo0]
            · linarith only [h162, h163, h4, hc35, hlam, hphi, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h209 | h209
            · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
              · rcases m.htr 1 2 5 (by decide) (by decide) with h211 | h211
                · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h213 | h213
                    · linarith only [h1, h213, h4, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                      · linarith only [h1, h162, h215, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h217 | h217
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h218 | h218
                          · rcases h5bigk with h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hlam, p219_0]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h162, hc15, hlam, hphi, p219_1, u5elo3]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h162, hc25, hlam, hphi, p219_1, u5elo3]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h162, hlam, p219_1]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h162, hc45, hlam, hphi, p219_1, u5elo3]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h0, hlam, p219_0]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hlam, p219_0]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hc25, hlam, hphi, p219_1, u5elo1]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h0, h162, hlam, p219_1]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h0, h162, hc45, hlam, hphi, p219_1, u5elo3]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h3, hlam, p219_1]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h211, hlam, p219_1]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hlam, p219_0]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h215, hlam, p219_1]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hc45, hlam, hphi, p219_1, u5elo2]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hc05, hlam, hphi, p219_1, u5elo3]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hc15, hlam, hphi, p219_1, u5elo3]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hc25, hlam, hphi, p219_1, u5elo3]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hlam, p219_0]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hc45, hlam, hphi, p219_1, u5elo3]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h209, hlam, p219_0]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h212, hlam, p219_0]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h217, hlam, p219_0]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [h218, hlam, p219_0]
                            · have p219_0 := h219c.1
                              have p219_1 := h219c.2.1
                              have p219_2 := h219c.2.2.1
                              have p219_3 := h219c.2.2.2
                              linarith only [hlam, p219_0]
                          · linarith only [h2, h217, h218, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h246 | h246
                          · rcases h5bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [hlam, p247_0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h212, h213, h217, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1, u0elo4]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h213, h217, hc23, hlam, hphi, ht34, ht45, p247_1, u5elo0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h162, hlam, p247_1]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h162, h213, h217, hc23, hlam, hphi, ht34, ht45, p247_1, u5elo3]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h0, hlam, p247_0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [hlam, p247_0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h213, h217, hc23, hlam, hphi, ht34, ht45, p247_1, u5elo1]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h0, h162, hlam, p247_1]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h0, h162, h213, h217, hc23, hlam, hphi, ht34, ht45, p247_1, u5elo3]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h3, hlam, p247_1]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h211, hlam, p247_1]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [hlam, p247_0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h215, hlam, p247_1]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h217, hlam, p247_1]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [hc05, hlam, hphi, p247_1, u5elo3]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h212, h213, h217, hc23, hlam, hphi, ht34, ht45, p247_1, u5elo3]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h213, h217, hc23, hlam, hphi, ht34, ht45, p247_1, u5elo3]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [hlam, p247_0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h213, h217, hc23, hlam, hphi, ht34, ht45, p247_1, u5elo3]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h209, hlam, p247_0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h212, hlam, p247_0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h2, h209, h213, h217, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p247_1, u2elo0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [h246, hlam, p247_0]
                            · have p247_0 := h247c.1
                              have p247_1 := h247c.2.1
                              have p247_2 := h247c.2.2.1
                              have p247_3 := h247c.2.2.2
                              linarith only [hlam, p247_0]
                          · linarith only [h209, h246, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                    · linarith only [h1, h209, h212, h274, h4, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h276 | h276
                      · linarith only [h162, h2, h209, h210, h212, h274, h276, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h278 | h278
                        · linarith only [h210, h212, h278, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h280 | h280
                          · rcases h5bigk with h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [hlam, p281_0]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [hc15, hlam, hphi, p281_1, u5elo0]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h162, h278, hc24, hlam, hphi, ht45, p281_1, u5elo3]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h162, hlam, p281_1]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h162, h212, hc14, hlam, hphi, ht45, p281_1, u5elo3]
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
                              linarith only [h278, hc24, hlam, hphi, ht45, p281_1, u5elo1]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h162, h2, h209, h212, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p281_1, u2elo0]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h212, hlam, p281_1]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h3, hlam, p281_1]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h211, hlam, p281_1]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [hlam, p281_0]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h276, hlam, p281_1]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h278, hlam, p281_1]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [hc05, hlam, hphi, p281_1, u5elo3]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [hc15, hlam, hphi, p281_1, u5elo3]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h274, h278, hc23, hlam, hphi, ht34, ht45, p281_1, u5elo3]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [hlam, p281_0]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [hc45, hlam, hphi, p281_1, u5elo3]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h209, hlam, p281_0]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h209, h211, h274, h278, hc23, hlam, hphi, ht34, ht45, p281_1, u5elo0]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h2, h209, h274, h278, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p281_1, u2elo0]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [h280, hlam, p281_0]
                            · have p281_0 := h281c.1
                              have p281_1 := h281c.2.1
                              have p281_2 := h281c.2.2.1
                              have p281_3 := h281c.2.2.2
                              linarith only [hlam, p281_0]
                          · linarith only [h209, h280, h4, hlam]
                · linarith only [h211, h3, hc12, hlam, hphi, u2elo0]
              · linarith only [h2, h210, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h310 | h310
              · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
                · rcases m.htr 1 4 5 (by decide) (by decide) with h312 | h312
                  · linarith only [h0, h209, h312, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h314 | h314
                    · linarith only [h1, h314, h4, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h316 | h316
                      · linarith only [h1, h162, h316, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h318 | h318
                        · linarith only [h2, h209, h318, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h320 | h320
                          · rcases h5bigk with h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [hlam, p321_0]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h311, hc25, hlam, hphi, p321_1, u5elo0]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h209, h320, hc25, hlam, hphi, p321_1, u5elo3]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h162, hlam, p321_1]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h209, hlam, p321_1]
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
                              linarith only [hc25, hlam, hphi, p321_1, u5elo1]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h0, h209, h320, hlam, p321_1]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h312, hlam, p321_1]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h3, hlam, p321_1]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h311, hlam, p321_1]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [hlam, p321_0]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h316, hlam, p321_1]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h318, hlam, p321_1]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [hc05, hlam, hphi, p321_1, u5elo3]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h311, h314, h318, hc23, hlam, hphi, ht34, ht45, p321_1, u5elo3]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h314, h318, hc23, hlam, hphi, ht34, ht45, p321_1, u5elo3]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [hlam, p321_0]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [hc45, hlam, hphi, p321_1, u5elo3]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h0, h311, h314, h318, hc23, hlam, hphi, ht34, ht45, p321_1, u5elo4]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h311, h314, h318, hc23, hlam, hphi, ht34, ht45, p321_1, u5elo4]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h314, h318, hc23, hlam, hphi, ht34, ht45, p321_1, u5elo4]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [h320, hlam, p321_0]
                            · have p321_0 := h321c.1
                              have p321_1 := h321c.2.1
                              have p321_2 := h321c.2.2.1
                              have p321_3 := h321c.2.2.2
                              linarith only [hlam, p321_0]
                          · linarith only [h320, h4, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h3, h311, hc12, hlam, hphi, u2elo0]
              · linarith only [h2, h310, hc12, hlam, hphi, u2elo0]
      · linarith only [h2, h3, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h351 | h351
      · rcases m.htr 0 3 4 (by decide) (by decide) with h352 | h352
        · linarith only [h1, h2, h352, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h354 | h354
          · rcases m.htr 0 4 5 (by decide) (by decide) with h355 | h355
            · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
              · linarith only [h1, h2, h356, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h358 | h358
                · rcases m.htr 1 4 5 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h360 | h360
                    · linarith only [h1, h352, h360, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h362 | h362
                      · linarith only [h1, h2, h362, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · linarith only [h1, h2, h354, h362, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h2, h355, h356, h359, hc12, hlam, hphi, u2elo3]
                · linarith only [h2, h351, h358, hc12, hlam, hphi, u2elo3]
            · linarith only [h2, h351, h355, hc25, hlam, hphi, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h368 | h368
            · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
              · linarith only [h1, h2, h369, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                · rcases m.htr 1 4 5 (by decide) (by decide) with h372 | h372
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                    · linarith only [h1, h352, h373, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h375 | h375
                      · linarith only [h1, h2, h375, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h377 | h377
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h378 | h378
                          · rcases h5bigk with h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [hlam, p379_0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [hc15, hlam, hphi, p379_1, u5elo0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h2, h351, h375, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p379_1, u2elo3]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h354, hlam, p379_1]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h2, h351, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p379_1, u2elo3]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h0, hlam, p379_0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [hlam, p379_0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h375, hc23, hlam, hphi, ht34, ht45, p379_1, u5elo1]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h0, h2, h351, h354, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p379_1, u2elo3]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h0, h2, h351, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p379_1, u2elo3]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h351, hlam, p379_1]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h371, hlam, p379_1]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [hlam, p379_0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h375, hlam, p379_1]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [hc45, hlam, hphi, p379_1, u5elo2]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [hc05, hlam, hphi, p379_1, u5elo3]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h371, h375, hc23, hlam, hphi, ht34, ht45, p379_1, u5elo3]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h375, hc23, hlam, hphi, ht34, ht45, p379_1, u5elo3]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [hlam, p379_0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [hc45, hlam, hphi, p379_1, u5elo3]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h368, hlam, p379_0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h372, hlam, p379_0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h377, hlam, p379_0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [h378, hlam, p379_0]
                            · have p379_0 := h379c.1
                              have p379_1 := h379c.2.1
                              have p379_2 := h379c.2.2.1
                              have p379_3 := h379c.2.2.2
                              linarith only [hlam, p379_0]
                          · linarith only [h2, h351, h373, h375, h378, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h2, h351, h372, h375, h377, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h2, h368, h369, h372, hc12, hlam, hphi, u2elo3]
                · linarith only [h2, h351, h371, hc12, hlam, hphi, u2elo3]
            · linarith only [h2, h351, h368, hc25, hlam, hphi, u5elo4]
      · linarith only [h1, h351, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h411 | h411
    · rcases m.htr 0 2 5 (by decide) (by decide) with h412 | h412
      · rcases m.htr 0 3 4 (by decide) (by decide) with h413 | h413
        · rcases m.htr 0 3 5 (by decide) (by decide) with h414 | h414
          · rcases m.htr 0 4 5 (by decide) (by decide) with h415 | h415
            · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
              · rcases m.htr 1 2 5 (by decide) (by decide) with h417 | h417
                · rcases m.htr 1 4 5 (by decide) (by decide) with h418 | h418
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
                        · linarith only [h1, h411, h421, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h1, h411, h415, h421, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h1, h420, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1, h413, h419, hlam]
                  · linarith only [h1, h411, h415, h418, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h416, h417, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h1, h411, h416, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
              · rcases m.htr 1 2 5 (by decide) (by decide) with h430 | h430
                · rcases m.htr 1 4 5 (by decide) (by decide) with h431 | h431
                  · linarith only [h0, h415, h431, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h433 | h433
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h434 | h434
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h435 | h435
                        · linarith only [h411, h415, h435, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h437 | h437
                          · linarith only [h411, h415, h433, h437, hlam]
                          · rcases h5bigk with h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hlam, p439_0]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hc15, hlam, hphi, p439_1, u5elo0]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h1, h412, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p439_1, u2elo2]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h1, h412, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p439_1, u2elo2]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h415, hlam, p439_1]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h0, hlam, p439_0]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hlam, p439_0]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h434, hc35, hlam, hphi, p439_1, u5elo1]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h0, h1, h412, h437, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p439_1, u2elo2]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h431, hlam, p439_1]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h412, hlam, p439_1]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h430, hlam, p439_1]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hlam, p439_0]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h437, hc34, hlam, hphi, ht45, p439_1, u5elo2]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h435, hlam, p439_1]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h414, hlam, p439_0]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hc15, hlam, hphi, p439_1, u5elo3]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h434, hlam, p439_0]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hlam, p439_0]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h437, hlam, p439_1]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hc05, hlam, hphi, p439_1, u5elo4]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hc15, hlam, hphi, p439_1, u5elo4]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [h434, hc35, hlam, hphi, p439_1, u5elo4]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hc35, hlam, hphi, p439_1, u5elo4]
                            · have p439_0 := h439c.1
                              have p439_1 := h439c.2.1
                              have p439_2 := h439c.2.2.1
                              have p439_3 := h439c.2.2.2
                              linarith only [hlam, p439_0]
                      · linarith only [h1, h434, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1, h413, h433, hlam]
                · linarith only [h1, h412, h430, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h411, h429, hc12, hlam, hphi, u2elo2]
          · linarith only [h1, h411, h414, hc24, hlam, hphi, ht45, u5elo3]
        · linarith only [h1, h411, h413, hlam]
      · linarith only [h411, h412, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h472 | h472
      · rcases m.htr 0 3 4 (by decide) (by decide) with h473 | h473
        · rcases m.htr 0 3 5 (by decide) (by decide) with h474 | h474
          · rcases m.htr 0 4 5 (by decide) (by decide) with h475 | h475
            · rcases m.htr 1 2 4 (by decide) (by decide) with h476 | h476
              · linarith only [h411, h476, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h478 | h478
                · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h480 | h480
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h481 | h481
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h482 | h482
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h483 | h483
                          · rcases h5bigk with h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h478, h481, h483, hc45, hlam, hphi, p484_1, u5elo0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h411, h472, h481, h483, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u2elo3]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h411, h472, h483, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u2elo3]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h411, h472, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u2elo3]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h0, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h481, h483, hc45, hlam, hphi, p484_1, u5elo1]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h0, h411, h472, h480, h483, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u2elo2]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h0, h411, h472, h480, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u2elo2]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h472, hlam, p484_1]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h478, hlam, p484_1]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h483, hc45, hlam, hphi, p484_1, u5elo2]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h411, h472, h480, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u2elo2]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h474, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hc15, hlam, hphi, p484_1, u5elo3]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h481, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h411, h472, h480, h481, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u2elo2]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h475, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h479, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h482, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h483, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                          · linarith only [h411, h472, h480, h482, h483, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · linarith only [h411, h475, h482, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h411, h480, h481, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1, h473, h480, hlam]
                  · linarith only [h1, h473, h475, h476, h479, hc12, hlam, hphi, u2elo2]
                · linarith only [h472, h478, hc12, hlam, hphi, u2elo0]
            · linarith only [h411, h472, h475, hc25, hlam, hphi, u5elo4]
          · linarith only [h1, h472, h474, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h518 | h518
          · rcases m.htr 0 4 5 (by decide) (by decide) with h519 | h519
            · rcases m.htr 1 2 4 (by decide) (by decide) with h520 | h520
              · linarith only [h411, h472, h520, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h522 | h522
                · rcases m.htr 1 4 5 (by decide) (by decide) with h523 | h523
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h524 | h524
                    · linarith only [h1, h472, h473, h524, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h526 | h526
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h527 | h527
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h528 | h528
                          · rcases h5bigk with h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h1, h472, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p529_1, u2elo2]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h1, h472, h524, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p529_1, u2elo3]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h1, h472, h524, h528, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p529_1, u2elo3]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h1, h472, h524, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p529_1, u2elo3]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h0, hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h526, h528, hc45, hlam, hphi, p529_1, u5elo1]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h0, h1, h472, h524, h528, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p529_1, u2elo3]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h0, h1, h472, h524, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p529_1, u2elo3]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h472, hlam, p529_1]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h522, hlam, p529_1]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h528, hc45, hlam, hphi, p529_1, u5elo2]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h1, h472, h524, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p529_1, u2elo3]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h518, hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [hc15, hlam, hphi, p529_1, u5elo3]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h526, hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [hc45, hlam, hphi, p529_1, u5elo3]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h519, hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h523, hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h527, hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [h528, hlam, p529_0]
                            · have p529_0 := h529c.1
                              have p529_1 := h529c.2.1
                              have p529_2 := h529c.2.2.1
                              have p529_3 := h529c.2.2.2
                              linarith only [hlam, p529_0]
                          · linarith only [h1, h473, h528, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h1, h472, h523, h524, h527, hlam]
                      · linarith only [h1, h472, h526, hc25, hlam, hphi, u5elo3]
                  · linarith only [h1, h472, h519, h520, h523, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h472, h522, hc12, hlam, hphi, u2elo2]
            · linarith only [h411, h472, h519, hc25, hlam, hphi, u5elo4]
          · linarith only [h1, h472, h518, hc25, hlam, hphi, u5elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h562 | h562
        · rcases m.htr 0 3 5 (by decide) (by decide) with h563 | h563
          · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
            · rcases m.htr 1 2 4 (by decide) (by decide) with h565 | h565
              · linarith only [h411, h565, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h567 | h567
                · linarith only [h472, h565, h567, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h569 | h569
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h570 | h570
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h571 | h571
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h572 | h572
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                          · rcases h5bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hc15, hlam, hphi, p574_1, u5elo0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h472, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h472, hc35, hlam, hphi, p574_1, u5elo2]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h472, hc45, hlam, hphi, p574_1, u5elo2]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h567, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h573, hc45, hlam, hphi, p574_1, u5elo1]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, h472, hc45, hlam, hphi, p574_1, u5elo2]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hc05, hlam, hphi, p574_1, u5elo2]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hc15, hlam, hphi, p574_1, u5elo2]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h573, hc45, hlam, hphi, p574_1, u5elo2]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hc45, hlam, hphi, p574_1, u5elo2]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h563, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h567, hc12, hlam, hphi, ht23, ht34, ht45, p574_1, u5elo3]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h571, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h563, hc45, hlam, hphi, p574_1, u5elo0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h564, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h569, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h572, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h573, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                          · rcases h5bigk with h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h472, h569, h573, hc34, hlam, hphi, ht45, p600_1, u5elo2]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h472, hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h472, hc35, hlam, hphi, p600_1, u5elo2]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h472, h573, hc34, hlam, hphi, ht45, p600_1, u5elo2]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h0, hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h567, hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h573, hc34, hlam, hphi, ht45, p600_1, u5elo1]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h573, hc34, hlam, hphi, ht45, p600_1, u5elo1]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [hc05, hlam, hphi, p600_1, u5elo2]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [hc15, hlam, hphi, p600_1, u5elo2]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h573, hc34, hlam, hphi, ht45, p600_1, u5elo2]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h573, hc34, hlam, hphi, ht45, p600_1, u5elo2]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h563, hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h569, h573, hc34, hlam, hphi, ht45, p600_1, u5elo3]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h571, hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h573, hlam, p600_1]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h564, hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h569, hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h572, hlam, p600_0]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [h411, h564, h570, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p600_1, u2elo2]
                            · have p600_0 := h600c.1
                              have p600_1 := h600c.2.1
                              have p600_2 := h600c.2.2.1
                              have p600_3 := h600c.2.2.2
                              linarith only [hlam, p600_0]
                        · linarith only [h411, h564, h572, hlam]
                      · linarith only [h411, h564, h570, h571, hc45, hlam, hphi, u5elo3]
                    · linarith only [h1, h562, h570, hlam]
                  · linarith only [h1, h562, h564, h565, h569, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h630 | h630
              · linarith only [h411, h630, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h632 | h632
                · linarith only [h472, h630, h632, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h634 | h634
                  · linarith only [h411, h564, h630, h634, hc02, hlam, hphi, u2elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h636 | h636
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h637 | h637
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h638 | h638
                        · linarith only [h411, h564, h636, h638, hc02, hlam, hphi, u2elo2]
                        · linarith only [h411, h638, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h1, h563, h637, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                    · linarith only [h1, h562, h636, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h562, h563, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
          · rcases m.htr 0 4 5 (by decide) (by decide) with h645 | h645
            · rcases m.htr 1 2 4 (by decide) (by decide) with h646 | h646
              · linarith only [h411, h646, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h648 | h648
                · linarith only [h472, h646, h648, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h650 | h650
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h651 | h651
                    · linarith only [h562, h644, h651, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h653 | h653
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h654 | h654
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h655 | h655
                          · rcases h5bigk with h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [hc15, hlam, hphi, p656_1, u5elo0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h472, hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h472, h655, hc45, hlam, hphi, p656_1, u5elo2]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h472, hc45, hlam, hphi, p656_1, u5elo2]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h0, hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h648, hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h655, hc45, hlam, hphi, p656_1, u5elo1]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h0, h472, hc45, hlam, hphi, p656_1, u5elo2]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [hc05, hlam, hphi, p656_1, u5elo2]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [hc15, hlam, hphi, p656_1, u5elo2]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h655, hc45, hlam, hphi, p656_1, u5elo2]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [hc45, hlam, hphi, p656_1, u5elo2]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h644, hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h644, h648, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p656_1, u0elo2]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h653, hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h644, hc45, hlam, hphi, p656_1, u5elo0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h645, hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h650, hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h654, hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [h655, hlam, p656_0]
                            · have p656_0 := h656c.1
                              have p656_1 := h656c.2.1
                              have p656_2 := h656c.2.2.1
                              have p656_3 := h656c.2.2.2
                              linarith only [hlam, p656_0]
                          · linarith only [h1, h644, h650, h651, h655, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h411, h472, h650, h654, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1, h653, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h411, h645, h646, h650, hc12, hlam, hphi, u2elo3]
            · linarith only [h562, h644, h645, hc35, hlam, hphi, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h687 | h687
            · rcases m.htr 1 2 4 (by decide) (by decide) with h688 | h688
              · linarith only [h411, h688, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h690 | h690
                · linarith only [h472, h688, h690, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h692 | h692
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h693 | h693
                    · linarith only [h1, h562, h693, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h695 | h695
                      · linarith only [h1, h644, h695, hc02, hlam, hphi, u2elo2]
                      · linarith only [h1, h695, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h411, h687, h688, h692, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h699 | h699
              · linarith only [h411, h699, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h701 | h701
                · linarith only [h472, h699, h701, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h703 | h703
                  · linarith only [h1, h562, h687, h699, h703, hc02, hlam, hphi, u2elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                    · linarith only [h1, h562, h705, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h707 | h707
                      · linarith only [h1, h644, h707, hc02, hlam, hphi, u2elo2]
                      · linarith only [h1, h707, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]

end R2N4
