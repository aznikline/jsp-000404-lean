import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_13_25_L_R_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h10, h11, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h10, h14, h9, hlam]
                        · rcases h5bigk with h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hc15, hlam, hphi, p16_1, u5elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hc25, hlam, hphi, p16_1, u5elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hc35, hlam, hphi, p16_1, u5elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h9, hc34, hlam, hphi, ht45, p16_1, u5elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h2, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h9, hc34, hlam, hphi, ht45, p16_1, u5elo1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h14, h2, hc34, hlam, hphi, ht45, p16_1, u5elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h2, h9, hc34, hlam, hphi, ht45, p16_1, u5elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h3, hlam, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hc15, hlam, hphi, p16_1, u5elo2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h14, h8, hc34, hlam, hphi, ht45, p16_1, u5elo1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, hlam, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, hphi, ht01, ht12, ht23, p16_1, u0ehi4, u3elo4]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h14, h8, hlam, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h1, h14, h7, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16_1, u3elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h14, hlam, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h4, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h8, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h1, h7, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16_1, u3elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h1, h7, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16_1, u3elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                    · linarith only [h1, h7, h9, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h0, h44, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                        · linarith only [h43, h46, h6, h8, hlam]
                        · rcases h5bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hc15, hlam, hphi, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h43, h44, hc34, hlam, hphi, ht45, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h46, hc34, hlam, hphi, ht45, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h43, h6, h8, hc34, hlam, hphi, ht45, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h2, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h43, h44, hc34, hlam, hphi, ht45, p48_1, u5elo1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h46, hc34, hlam, hphi, ht45, p48_1, u5elo1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h8, hlam, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h3, hlam, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hc15, hlam, hphi, p48_1, u5elo2]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h4, h44, h46, hc34, hlam, hphi, ht45, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h44, hlam, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, hphi, ht01, ht12, ht23, p48_1, u0ehi4, u3elo4]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h4, h43, h46, h6, h8, hc34, hlam, hphi, ht45, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h4, h46, hc25, hlam, hphi, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h46, hlam, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h4, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h4, h43, h6, h8, hc34, hlam, hphi, ht45, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h4, hc25, hlam, hphi, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h4, hc35, hlam, hphi, p48_1, u5elo0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                    · linarith only [h1, h43, h7, hc23, hlam, hphi, u3elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                    · linarith only [h7, h76, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                        · rcases h5bigk with h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hlam, p80_0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h75, hc45, hlam, hphi, p80_1, u5elo0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h78, hc45, hlam, hphi, p80_1, u5elo0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h79, hc45, hlam, hphi, p80_1, u5elo0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hc45, hlam, hphi, p80_1, u5elo0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h2, hlam, p80_0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hlam, p80_0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h78, hc45, hlam, hphi, p80_1, u5elo1]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h79, hc45, hlam, hphi, p80_1, u5elo1]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, p80_1, u5elo0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h3, hlam, p80_1]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hc15, hlam, hphi, p80_1, u5elo2]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hlam, p80_0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h79, hc45, hlam, hphi, p80_1, u5elo2]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h0, h6, h78, hc01, hc45, hlam, hphi, ht0b, ht5b, p80_1]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hlam, hphi, ht01, ht12, ht23, p80_1, u0ehi4, u3elo4]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h75, hc45, hlam, hphi, p80_1, u5elo3]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hc25, hlam, hphi, p80_1, u5elo3]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hlam, p80_0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hc45, hlam, hphi, p80_1, u5elo3]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h4, hlam, p80_0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h75, hlam, p80_0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h78, hlam, p80_0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [h79, hlam, p80_0]
                          · have p80_0 := h80c.1
                            have p80_1 := h80c.2.1
                            have p80_2 := h80c.2.2.1
                            have p80_3 := h80c.2.2.2
                            linarith only [hlam, p80_0]
                        · linarith only [h5, h7, h75, h79, hc23, hlam, hphi, ht34, ht45, u5elo1]
                      · linarith only [h7, h75, h76, h78, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                    · linarith only [h108, h5, h7, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h110 | h110
                      · linarith only [h0, h110, h6, h75, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                        · linarith only [h112, h5, h7, h75, hc23, hlam, hphi, u3elo3]
                        · linarith only [h112, h5, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                · linarith only [h115, h5, h6, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                    · linarith only [h115, h118, hc13, hlam, hphi, u3elo2]
                    · linarith only [h118, h5, h6, hc23, hlam, hphi, u3elo3]
                  · linarith only [h117, h5, h6, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                      · linarith only [h122, h126, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h122, h124, h125, h126, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h125, h5, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h131 | h131
                      · linarith only [h122, h124, h131, h5, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h133 | h133
                        · linarith only [h122, h124, h130, h133, hlam]
                        · rcases h5bigk with h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h122, h124, h130, hc34, hlam, hphi, ht45, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hc25, hlam, hphi, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hc35, hlam, hphi, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h122, h124, h130, hc34, hlam, hphi, ht45, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h2, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h130, h131, hc34, hlam, hphi, ht45, p135_1, u5elo1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h133, hc34, hlam, hphi, ht45, p135_1, u5elo1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h124, hlam, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h3, hlam, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hc15, hlam, hphi, p135_1, u5elo2]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h131, h133, h4, hc34, hlam, hphi, ht45, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h131, hlam, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, hphi, ht01, ht12, ht23, p135_1, u0ehi4, u3elo4]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h122, h124, h130, h133, h4, hc34, hlam, hphi, ht45, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h133, h4, hc25, hlam, hphi, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h133, hlam, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h4, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h122, h124, h130, h4, hc34, hlam, hphi, ht45, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h4, hc25, hlam, hphi, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h4, hc35, hlam, hphi, p135_1, u5elo0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                    · linarith only [h130, h5, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h122, h123, h5, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                        · rcases h5bigk with h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hc15, hlam, hphi, p168_1, u5elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h166, hc45, hlam, hphi, p168_1, u5elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h167, hc45, hlam, hphi, p168_1, u5elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hc45, hlam, hphi, p168_1, u5elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h2, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h166, hc45, hlam, hphi, p168_1, u5elo1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h167, h2, hc45, hlam, hphi, p168_1, u5elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, p168_1, u5elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h3, hlam, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hc15, hlam, hphi, p168_1, u5elo2]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h167, h3, hc45, hlam, hphi, p168_1, u5elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h3, hc45, hlam, hphi, p168_1, u5elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, hphi, ht01, ht12, ht23, p168_1, u0ehi4, u3elo4]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h163, h164, h167, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p168_1, u3elo1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h1, h163, h167, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p168_1, u3elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h1, h163, h167, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p168_1, u3elo0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h4, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h164, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h166, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h167, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                        · rcases h5bigk with h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [hlam, p194_0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h164, h167, hc34, hlam, hphi, ht45, p194_1, u5elo0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h166, h167, hc34, hlam, hphi, ht45, p194_1, u5elo0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [hc35, hlam, hphi, p194_1, u5elo0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h167, hc34, hlam, hphi, ht45, p194_1, u5elo0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h2, hlam, p194_0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [hlam, p194_0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h166, h167, hc34, hlam, hphi, ht45, p194_1, u5elo1]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h167, h2, hc34, hlam, hphi, ht45, p194_1, u5elo0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h167, h2, hc34, hlam, hphi, ht45, p194_1, u5elo0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h3, hlam, p194_1]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [hc15, hlam, hphi, p194_1, u5elo2]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [hlam, p194_0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h167, h3, hc34, hlam, hphi, ht45, p194_1, u5elo0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h167, h3, hc34, hlam, hphi, ht45, p194_1, u5elo0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [hlam, hphi, ht01, ht12, ht23, p194_1, u0ehi4, u3elo4]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h164, h167, hlam, p194_1]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h164, h167, hc25, hlam, hphi, p194_1, u5elo1]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [hlam, p194_0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h167, hlam, p194_1]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h4, hlam, p194_0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h164, hlam, p194_0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h166, hlam, p194_0]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [h164, hc35, hlam, hphi, p194_1, u5elo1]
                          · have p194_0 := h194c.1
                            have p194_1 := h194c.2.1
                            have p194_2 := h194c.2.2.1
                            have p194_3 := h194c.2.2.2
                            linarith only [hlam, p194_0]
                      · linarith only [h122, h164, h166, hlam]
                    · linarith only [h165, h5, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
                      · linarith only [h122, h164, h222, h223, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h122, h223, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h222, h5, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h227 | h227
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                    · linarith only [h163, h228, hc13, hlam, hphi, u3elo2]
                    · linarith only [h228, h5, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
                    · linarith only [h163, h231, h5, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h231, h5, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo1]
    · linarith only [h0, h1, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h238 | h238
    · rcases m.htr 0 1 5 (by decide) (by decide) with h239 | h239
      · rcases m.htr 0 2 5 (by decide) (by decide) with h240 | h240
        · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
          · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
            · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
              · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
                · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h247 | h247
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                        · linarith only [h0, h238, h242, h246, h248, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h238, h244, h245, h248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h238, h244, h245, h247, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h238, h244, h246, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h254 | h254
                      · linarith only [h243, h245, h254, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h256 | h256
                        · linarith only [h245, h253, h256, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · rcases h5bigk with h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [hlam, p258_0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [hc15, hlam, hphi, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [hc25, hlam, hphi, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h256, hc34, hlam, hphi, ht45, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h243, h245, h253, hc34, hlam, hphi, ht45, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h239, hlam, p258_0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [hlam, p258_0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h253, h254, hc34, hlam, hphi, ht45, p258_1, u5elo1]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h256, hc34, hlam, hphi, ht45, p258_1, u5elo1]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h245, hlam, p258_1]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h240, hlam, p258_1]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [hc15, hlam, hphi, p258_1, u5elo2]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [hlam, p258_0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h241, h254, h256, hc34, hlam, hphi, ht45, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h254, hlam, p258_1]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [hlam, hphi, ht01, ht12, ht23, p258_1, u0ehi4, u3elo4]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h241, h243, h245, h253, h256, hc34, hlam, hphi, ht45, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h241, h256, hc25, hlam, hphi, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [hlam, p258_0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h256, hlam, p258_1]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h241, hlam, p258_0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h241, h243, h245, h253, hc34, hlam, hphi, ht45, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h241, hc25, hlam, hphi, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [h241, hc35, hlam, hphi, p258_1, u5elo0]
                          · have p258_0 := h258c.1
                            have p258_1 := h258c.2.1
                            have p258_2 := h258c.2.2.1
                            have p258_3 := h258c.2.2.2
                            linarith only [hlam, p258_0]
                    · linarith only [h0, h238, h244, h253, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h285 | h285
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h286 | h286
                    · linarith only [h244, h286, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h288 | h288
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h289 | h289
                        · rcases h5bigk with h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hlam, p290_0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hc15, hlam, hphi, p290_1, u5elo0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h288, hc45, hlam, hphi, p290_1, u5elo0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h289, hc45, hlam, hphi, p290_1, u5elo0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hc45, hlam, hphi, p290_1, u5elo0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h239, hlam, p290_0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hlam, p290_0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h288, hc45, hlam, hphi, p290_1, u5elo1]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h289, hc45, hlam, hphi, p290_1, u5elo1]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h0, h239, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p290_1]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h240, hlam, p290_1]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hc15, hlam, hphi, p290_1, u5elo2]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hlam, p290_0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h240, h289, hc45, hlam, hphi, p290_1, u5elo0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h240, hc45, hlam, hphi, p290_1, u5elo0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hlam, hphi, ht01, ht12, ht23, p290_1, u0ehi4, u3elo4]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h285, hc45, hlam, hphi, p290_1, u5elo3]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hc25, hlam, hphi, p290_1, u5elo3]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hlam, p290_0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hc45, hlam, hphi, p290_1, u5elo3]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h241, hlam, p290_0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h285, hlam, p290_0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h288, hlam, p290_0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [h289, hlam, p290_0]
                          · have p290_0 := h290c.1
                            have p290_1 := h290c.2.1
                            have p290_2 := h290c.2.2.1
                            have p290_3 := h290c.2.2.2
                            linarith only [hlam, p290_0]
                        · linarith only [h244, h285, h289, hc13, hlam, hphi, ht34, ht45, u5elo1]
                      · linarith only [h244, h285, h286, h288, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h318 | h318
                    · linarith only [h242, h244, h318, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h320 | h320
                      · linarith only [h243, h285, h320, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h322 | h322
                        · linarith only [h242, h244, h285, h322, hc23, hlam, hphi, u3elo3]
                        · linarith only [h242, h244, h322, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h243, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h238, h242, hc23, hlam, hphi, ht01, ht12, u0ehi2]
          · linarith only [h241, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
        · linarith only [h0, h238, h240, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo2]
      · linarith only [h238, h239, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo1]
    · linarith only [h238, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h2, h3, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
              · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h0, h10, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h12, h13, h3, h6, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h15, h3, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h0, h12, h15, h3, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h1, h12, h18, h5, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                        · linarith only [h12, h20, h8, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                          · linarith only [h12, h2, h22, h3, h5, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                            · linarith only [h0, h24, h3, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                              · linarith only [h2, h24, h26, h3, h5, hlam]
                              · rcases h4bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h2, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28_1, u2elo4]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h2, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28_1, u2elo4]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h12, h2, h3, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p28_1, u2elo4]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h6, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h1, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h1, h2, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28_1, u2elo4]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h12, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h18, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h2, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h9, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h20, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h24, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h5, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h2, h3, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28_1, u2elo4]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h2, h3, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28_1, u2elo4]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h26, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h12, h5, h8, hc23, hc45, hlam, hphi, ht34, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  rcases p28_3 (m.d 0 4) (by simp) with h50 | h50
                                  · linarith only [h50, h6, hlam]
                                  · linarith only [h1, h50, hlam]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  rcases p28_3 (m.d 0 4) (by simp) with h53 | h53
                                  · linarith only [h53, h6, hlam]
                                  · linarith only [h2, h53, hlam]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h12, h8, hc23, hc45, hlam, hphi, ht34, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                · linarith only [h2, h3, h9, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                  · linarith only [h3, h60, h8, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h63 | h63
                      · linarith only [h1, h63, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h66 | h66
                          · linarith only [h66, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                            · linarith only [h0, h59, h6, h68, hc02, hlam, hphi, ht0b, ht5b, u5ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                              · linarith only [h0, h3, h59, h65, h68, h70, hlam]
                              · linarith only [h59, h66, h70, h8, hc24, hc45, hlam, hphi]
                        · linarith only [h5, h59, h65, h8, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h2, h3, h5, h59, h62, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h2, h3, h59, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
            · linarith only [h2, h3, h76, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
              · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                  · linarith only [h3, h80, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                    · linarith only [h0, h3, h5, h78, h82, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                      · linarith only [h1, h76, h84, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                        · linarith only [h0, h3, h5, h78, h86, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                          · linarith only [h0, h3, h79, h86, h88, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                            · linarith only [h0, h3, h76, h79, h90, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                              · linarith only [h0, h3, h79, h86, h90, h92, hc23, hc34, hlam, hphi]
                              · rcases h4bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h2, h3, h78, h82, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p94_1, u2elo4]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h2, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p94_1, u2elo4]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h5, hlam, p94_1]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h76, hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h1, hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h1, h2, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p94_1, u2elo4]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h82, hlam, p94_1]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h84, hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h2, hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h79, hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h86, hlam, p94_1]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h90, hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h1, h92, hc14, hc45, hlam, hphi, p94_1]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h79, h92, hc24, hc45, hlam, hphi, p94_1]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h92, hc24, hc45, hlam, hphi, p94_1]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h92, hlam, p94_0]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  rcases p94_3 (m.d 0 4) (by simp) with h115 | h115
                                  · linarith only [h115, hlam, p94_0]
                                  · rcases p94_3 (m.d 1 4) (by simp) with h117 | h117
                                    · linarith only [h117, h84, hlam]
                                    · rcases p94_3 (m.d 2 4) (by simp) with h119 | h119
                                      · linarith only [h119, h90, hlam]
                                      · rcases p94_3 (m.d 3 4) (by simp) with h121 | h121
                                        · linarith only [h121, h92, hlam]
                                        · linarith only [h121, h5, hlam]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  rcases p94_3 (m.d 0 4) (by simp) with h124 | h124
                                  · linarith only [h124, h76, hlam]
                                  · linarith only [h1, h124, hlam]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  rcases p94_3 (m.d 0 4) (by simp) with h127 | h127
                                  · linarith only [h127, h76, hlam]
                                  · linarith only [h127, h2, hlam]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [h5, hc03, hc45, hlam, hphi, ht34, p94_1]
                                · have p94_0 := h94c.1
                                  have p94_1 := h94c.2.1
                                  have p94_2 := h94c.2.2.1
                                  have p94_3 := h94c.2.2.2
                                  linarith only [hlam, p94_0]
                · linarith only [h2, h3, h79, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                  · linarith only [h134, h3, h78, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                    · linarith only [h1, h136, h5, hlam]
                    · linarith only [h133, h136, h78, hlam]
                · linarith only [h133, h2, h3, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h140 | h140
        · linarith only [h140, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h142 | h142
          · rcases m.htr 0 4 5 (by decide) (by decide) with h143 | h143
            · linarith only [h143, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
              · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                · linarith only [h0, h146, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
                  · linarith only [h0, h140, h148, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                    · linarith only [h145, h146, h150, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                      · linarith only [h1, h152, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                        · linarith only [h145, h146, h150, h154, hlam]
                        · linarith only [h0, h142, h143, h145, h154, h2, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                · linarith only [h0, h157, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                  · linarith only [h0, h140, h159, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                      · linarith only [h1, h162, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h165 | h165
                          · linarith only [h165, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                            · linarith only [h164, h165, h167, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h169 | h169
                              · linarith only [h161, h169, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases h4bigk with h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h143, h161, hc34, hc45, hlam, hphi, p171_1]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h2, hlam, p171_1]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h143, hc34, hc45, hlam, hphi, p171_1]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h143, hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h1, hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h157, hlam, p171_1]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h1, h143, hc34, hc45, hlam, hphi, p171_1]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h162, hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h0, h2, hc12, hlam, hphi, p171_1, u2elo3]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h157, hc12, hlam, hphi, p171_1, u2elo3]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h164, h165, h169, hc34, hc45, hlam, hphi, p171_1]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h167, hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h142, hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h161, hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h164, hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h169, hlam, p171_0]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  rcases p171_3 (m.d 0 4) (by simp) with h192 | h192
                                  · linarith only [h192, hlam, p171_0]
                                  · rcases p171_3 (m.d 1 4) (by simp) with h194 | h194
                                    · linarith only [h162, h194, hlam]
                                    · rcases p171_3 (m.d 2 4) (by simp) with h196 | h196
                                      · linarith only [h167, h196, hlam]
                                      · linarith only [h196, h2, hlam]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  rcases p171_3 (m.d 0 4) (by simp) with h199 | h199
                                  · linarith only [h143, h199, hlam]
                                  · linarith only [h1, h199, hlam]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [h0, h2, hc12, hc45, hlam, hphi, ht23, ht34, p171_1]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  rcases p171_3 (m.d 0 4) (by simp) with h203 | h203
                                  · linarith only [h143, h203, hlam]
                                  · linarith only [h142, h203, hlam]
                                · have p171_0 := h171c.1
                                  have p171_1 := h171c.2.1
                                  have p171_2 := h171c.2.2.1
                                  have p171_3 := h171c.2.2.2
                                  linarith only [hlam, p171_0]
                        · linarith only [h142, h145, h164, h2, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h208 | h208
                      · linarith only [h1, h208, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                        · linarith only [h145, h161, h210, hc12, hlam, hphi, u2elo2]
                        · linarith only [h142, h145, h2, h210, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h213 | h213
            · linarith only [h2, h213, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h215 | h215
              · rcases m.htr 1 2 4 (by decide) (by decide) with h216 | h216
                · linarith only [h0, h2, h216, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
                  · linarith only [h0, h2, h218, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h220 | h220
                    · linarith only [h0, h142, h2, h215, h220, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h1, h213, h222, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                        · linarith only [h0, h2, h215, h220, h224, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                          · linarith only [h0, h2, h215, h226, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                            · linarith only [h2, h213, h228, hc02, hlam, hphi, u2elo3]
                            · linarith only [h0, h2, h215, h228, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
                · linarith only [h0, h2, h231, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h233 | h233
                  · linarith only [h0, h140, h233, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
                    · linarith only [h1, h142, h235, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                      · linarith only [h1, h237, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                        · linarith only [h215, h235, h239, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                          · linarith only [h241, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
                            · linarith only [h243, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
                              · linarith only [h0, h2, h243, h245, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h215, h239, h245, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
      · linarith only [h0, h1, h248, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h250 | h250
        · linarith only [h248, h250, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
          · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
            · linarith only [h248, h253, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
              · linarith only [h0, h1, h253, h255, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h257 | h257
                · linarith only [h0, h1, h248, h253, h257, hc02, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h0, h1, h257, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h260 | h260
            · linarith only [h248, h260, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
              · linarith only [h0, h1, h260, h262, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h264 | h264
                · linarith only [h0, h1, h260, h264, hc24, hc45, hlam, hphi]
                · linarith only [h0, h1, h264, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h267 | h267
    · rcases m.htr 0 2 4 (by decide) (by decide) with h268 | h268
      · rcases m.htr 0 2 5 (by decide) (by decide) with h269 | h269
        · linarith only [h269, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h271 | h271
          · rcases m.htr 0 4 5 (by decide) (by decide) with h272 | h272
            · linarith only [h0, h267, h272, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
              · rcases m.htr 1 2 4 (by decide) (by decide) with h275 | h275
                · rcases m.htr 1 2 5 (by decide) (by decide) with h276 | h276
                  · linarith only [h0, h267, h269, h275, h276, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h267, h275, h276, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h0, h267, h275, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
              · linarith only [h0, h267, h274, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h281 | h281
            · linarith only [h0, h267, h281, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
              · rcases m.htr 1 2 4 (by decide) (by decide) with h284 | h284
                · rcases m.htr 1 2 5 (by decide) (by decide) with h285 | h285
                  · linarith only [h0, h269, h285, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h267, h284, h285, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h0, h267, h284, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
              · linarith only [h0, h267, h283, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
      · linarith only [h0, h267, h268, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h291 | h291
      · rcases m.htr 0 2 5 (by decide) (by decide) with h292 | h292
        · linarith only [h292, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h294 | h294
          · rcases m.htr 0 4 5 (by decide) (by decide) with h295 | h295
            · linarith only [h291, h292, h295, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h297 | h297
              · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                · rcases m.htr 1 2 5 (by decide) (by decide) with h299 | h299
                  · linarith only [h267, h291, h292, h299, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h299, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h298, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h297, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h304 | h304
            · linarith only [h291, h292, h304, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
              · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
                · rcases m.htr 1 2 5 (by decide) (by decide) with h308 | h308
                  · linarith only [h292, h308, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h308, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h307, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h306, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h313 | h313
        · linarith only [h291, h313, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
          · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
            · linarith only [h291, h316, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
              · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                · linarith only [h291, h319, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h319, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h318, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h323 | h323
            · linarith only [h291, h323, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
              · rcases m.htr 1 2 4 (by decide) (by decide) with h326 | h326
                · linarith only [h0, h291, h326, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h326, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h325, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
