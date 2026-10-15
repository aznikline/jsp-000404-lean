import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_15_M_LR_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h0, h4, h5, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h3, h5, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, h2, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                · linarith only [h0, h13, h2, h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h0, h16, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h15, h16, h18, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h0, h11, h15, h16, h18, h20, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases h2bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            rcases p22_3 (m.d 0 2) (by simp) with h24 | h24
                            · rcases p22_3 (m.d 1 2) (by simp) with h25 | h25
                              · linarith only [h0, h25, hlam]
                              · rcases p22_3 (m.d 2 3) (by simp) with h27 | h27
                                · linarith only [h2, h27, hlam]
                                · linarith only [h27, h5, hlam]
                            · linarith only [h0, h24, hlam]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h15, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1, u0elo0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h11, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22_1, u0elo0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h13, hlam, hphi, ht0b, ht5b, p22_1, u0elo0, u5ehi1]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, hlam, p22_1]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h5, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h11, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h13, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h2, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h16, hc12, hc35, hlam, hphi, ht23, p22_1]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h11, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22_1, u0elo0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h16, hlam, p22_1]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h3, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22_1, u0elo0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h15, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h18, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h4, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22_1, u0elo0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22_1, u0elo0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h11, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22_1, u0elo0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                    · linarith only [h0, h2, h54, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h0, h3, h56, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                        · linarith only [h15, h5, h56, h58, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h15, h5, h58, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
            · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
              · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                · linarith only [h0, h4, h63, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                  · linarith only [h1, h61, h63, h65, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                    · linarith only [h1, h62, h63, h65, h67, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                      · linarith only [h1, h62, h63, h69, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                        · linarith only [h2, h4, h69, h71, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                        · rcases h2bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h4, h67, h71, hc12, hc45, hlam, hphi, ht23, ht34, p73_1]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h4, h67, h71, hc23, hc45, hlam, hphi, ht34, p73_1]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h4, h65, h67, h71, hc23, hc45, hlam, hphi, ht34, p73_1]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h4, hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h0, hlam, p73_1]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h0, h2, h4, h67, h71, hc23, hc45, hlam, hphi, ht34, p73_1, u0ehi7, u0elo0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h0, h2, h4, h65, h67, h71, hc23, hc45, hlam, hphi, ht34, p73_1, u0ehi7, u0elo0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h63, hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h2, hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h61, hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h65, hlam, p73_1]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h67, hlam, p73_1]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h3, hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h62, hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h3, h4, h67, h71, hc23, hc45, hlam, hphi, ht34, p73_1]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h69, hlam, p73_0]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h2, h67, h71, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p73_1, u0ehi7]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [h62, h67, h71, hc24, hc45, hlam, hphi, p73_1]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            rcases p73_3 (m.d 0 2) (by simp) with h96 | h96
                            · linarith only [h4, h96, hlam]
                            · linarith only [h2, h96, hlam]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            rcases p73_3 (m.d 0 2) (by simp) with h99 | h99
                            · linarith only [h4, h99, hlam]
                            · linarith only [h3, h99, hlam]
                          · have p73_0 := h73c.1
                            have p73_1 := h73c.2.1
                            have p73_2 := h73c.2.2.1
                            have p73_3 := h73c.2.2.2
                            linarith only [hlam, p73_0]
              · linarith only [h3, h4, h62, hc12, hc25, hlam, hphi]
            · linarith only [h2, h4, h61, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h105 | h105
          · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
            · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
              · linarith only [h105, h107, h3, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                · linarith only [h0, h109, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h105, h109, h3, hc12, hc24, hlam, hphi]
            · linarith only [h106, h2, h3, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
            · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
              · linarith only [h0, h114, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                · linarith only [h0, h105, h116, h2, hlam, hphi, u0ehi7, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                  · linarith only [h1, h113, h116, h118, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                    · linarith only [h1, h113, h116, h120, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h122 | h122
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                        · rcases h2bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h105, h118, h122, hc12, hc34, hlam, hphi, ht23, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h105, h118, h122, hc23, hc34, hlam, hphi, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h3, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h105, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h0, hlam, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h0, h105, h118, h122, h2, hc23, hc34, hlam, hphi, p124_1, u0ehi7, u0elo0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h114, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h116, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h2, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h113, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h118, hlam, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h120, hlam, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h118, h2, hc34, hlam, hphi, ht01, ht12, ht23, p124_1, u0ehi7]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h113, h118, hc23, hc34, hlam, hphi, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            rcases p124_3 (m.d 0 2) (by simp) with h142 | h142
                            · linarith only [h142, h3, hlam]
                            · linarith only [h142, h2, hlam]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h105, h118, h2, hc34, hlam, hphi, ht01, ht12, ht23, p124_1, u0ehi7]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h2, hc25, hlam, hphi, ht01, ht12, p124_1, u0ehi7]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h113, h120, hc23, hc35, hlam, hphi, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            rcases p124_3 (m.d 0 2) (by simp) with h149 | h149
                            · linarith only [h105, h149, hlam]
                            · linarith only [h149, h2, hlam]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h122, hlam, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                        · linarith only [h118, h122, h123, hlam]
                      · linarith only [h122, h2, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
            · linarith only [h113, h2, h3, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h157 | h157
        · rcases m.htr 0 2 5 (by decide) (by decide) with h158 | h158
          · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
            · linarith only [h158, h159, h2, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h161 | h161
              · rcases m.htr 1 2 5 (by decide) (by decide) with h162 | h162
                · linarith only [h0, h162, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h158, h162, h2, hc12, hc23, hlam, hphi]
              · linarith only [h157, h161, h2, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
            · linarith only [h166, h2, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
              · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                · linarith only [h0, h157, h158, h169, hlam, hphi, u0ehi8, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h171 | h171
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h172 | h172
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
                      · linarith only [h1, h168, h169, h173, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                        · linarith only [h1, h157, h158, h168, h169, h171, h173, h175, hlam, hphi, u0ehi8, u0elo0]
                        · rcases h2bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h158, h173, hc12, hc45, hlam, hphi, ht23, ht34, p177_1]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h2, hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h158, h171, h173, hc34, hc45, hlam, hphi, p177_1]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h158, hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h0, hlam, p177_1]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h166, hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h0, h157, h158, h171, h173, hc34, hc45, hlam, hphi, p177_1, u0ehi8, u0elo0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h169, hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h157, hc23, hlam, hphi, ht01, ht12, p177_1, u0ehi8]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            rcases p177_3 (m.d 0 2) (by simp) with h189 | h189
                            · linarith only [h189, h2, hlam]
                            · linarith only [h0, h189, hlam]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            rcases p177_3 (m.d 0 2) (by simp) with h193 | h193
                            · linarith only [h193, h2, hlam]
                            · linarith only [h157, h193, hlam]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h157, h158, hc23, hlam, hphi, ht01, ht12, p177_1, u0ehi8]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h157, hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h168, hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h171, hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h173, hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h157, h173, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p177_1, u0ehi8]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h168, h173, hc24, hc45, hlam, hphi, p177_1]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [h172, hlam, p177_0]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            rcases p177_3 (m.d 0 2) (by simp) with h205 | h205
                            · linarith only [h158, h205, hlam]
                            · linarith only [h157, h205, hlam]
                          · have p177_0 := h177c.1
                            have p177_1 := h177c.2.1
                            have p177_2 := h177c.2.2.1
                            have p177_3 := h177c.2.2.2
                            linarith only [hlam, p177_0]
                    · linarith only [h157, h172, h2, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                  · linarith only [h157, h171, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
              · linarith only [h157, h168, h2, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h212 | h212
          · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
            · linarith only [h2, h212, h213, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
              · linarith only [h0, h157, h212, h215, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h217 | h217
                · linarith only [h0, h217, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h2, h212, h217, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
            · linarith only [h2, h220, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
              · linarith only [h0, h157, h222, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                · linarith only [h0, h212, h224, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                        · rcases h2bigk with h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h212, h226, h228, hc12, hc23, hlam, hphi, p230_1]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h2, hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h157, hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h212, hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h0, hlam, p230_1]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h220, hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h222, hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h224, hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p230_1, u0ehi6]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            rcases p230_3 (m.d 0 2) (by simp) with h242 | h242
                            · linarith only [h2, h242, hlam]
                            · linarith only [h0, h242, hlam]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h157, hc23, hlam, hphi, ht01, ht12, p230_1, u0ehi6]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h212, hc23, hlam, hphi, ht01, ht12, p230_1, u0ehi6]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p230_1, u0ehi6]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            rcases p230_3 (m.d 0 2) (by simp) with h249 | h249
                            · linarith only [h157, h249, hlam]
                            · linarith only [h0, h249, hlam]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h226, hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h212, h226, hc23, hlam, hphi, ht01, ht12, p230_1, u0ehi6]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht12, p230_1, u0ehi6]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            rcases p230_3 (m.d 0 2) (by simp) with h256 | h256
                            · linarith only [h212, h256, hlam]
                            · linarith only [h0, h256, hlam]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h227, hlam, p230_0]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [h228, hlam, p230_1]
                          · have p230_0 := h230c.1
                            have p230_1 := h230c.2.1
                            have p230_2 := h230c.2.2.1
                            have p230_3 := h230c.2.2.2
                            linarith only [hlam, p230_0]
                        · rcases h2bigk with h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h2, hc12, hc23, hlam, hphi, p262_1]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h2, hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h157, hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h212, hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h0, hlam, p262_1]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h220, hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h222, hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h224, hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p262_1, u0ehi6]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            rcases p262_3 (m.d 0 2) (by simp) with h274 | h274
                            · linarith only [h2, h274, hlam]
                            · linarith only [h0, h274, hlam]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h157, hc23, hlam, hphi, ht01, ht12, p262_1, u0ehi6]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h212, hc23, hlam, hphi, ht01, ht12, p262_1, u0ehi6]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p262_1, u0ehi6]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            rcases p262_3 (m.d 0 2) (by simp) with h281 | h281
                            · linarith only [h157, h281, hlam]
                            · linarith only [h0, h281, hlam]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h226, hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h212, h226, hc23, hlam, hphi, ht01, ht12, p262_1, u0ehi6]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht12, p262_1, u0ehi6]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            rcases p262_3 (m.d 0 2) (by simp) with h288 | h288
                            · linarith only [h212, h288, hlam]
                            · linarith only [h0, h288, hlam]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h227, hlam, p262_0]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [h228, hlam, p262_1]
                          · have p262_0 := h262c.1
                            have p262_1 := h262c.2.1
                            have p262_2 := h262c.2.2.1
                            have p262_3 := h262c.2.2.2
                            linarith only [hlam, p262_0]
                      · linarith only [h157, h228, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h2, h227, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h2, h226, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h297 | h297
      · rcases m.htr 0 2 4 (by decide) (by decide) with h298 | h298
        · rcases m.htr 0 2 5 (by decide) (by decide) with h299 | h299
          · linarith only [h0, h1, h299, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
            · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
              · rcases m.htr 1 2 5 (by decide) (by decide) with h303 | h303
                · linarith only [h0, h299, h303, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h305 | h305
                  · linarith only [h0, h1, h301, h303, h305, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                    · linarith only [h0, h1, h302, h303, h305, h307, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1, h302, h303, h305, h307, hc23, hc35, hlam, hphi]
              · linarith only [h298, h299, h302, hc12, hc25, hlam, hphi]
            · linarith only [h297, h299, h301, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h312 | h312
          · linarith only [h0, h1, h312, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
            · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
              · linarith only [h298, h315, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                · linarith only [h0, h1, h297, h312, h317, hc15, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                  · linarith only [h0, h1, h314, h317, h319, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
                    · linarith only [h0, h1, h314, h317, h321, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1, h314, h317, h321, hc23, hc35, hlam, hphi]
            · linarith only [h297, h298, h314, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h325 | h325
        · rcases m.htr 0 2 5 (by decide) (by decide) with h326 | h326
          · linarith only [h0, h1, h326, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h328 | h328
            · linarith only [h297, h328, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h330 | h330
              · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                · linarith only [h0, h325, h326, h331, hlam, hphi, u0ehi8, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h333 | h333
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h334 | h334
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h335 | h335
                      · linarith only [h0, h1, h330, h331, h334, h335, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1, h330, h331, h335, hc24, hc45, hlam, hphi]
                    · linarith only [h297, h325, h334, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                  · linarith only [h297, h325, h333, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
              · linarith only [h297, h325, h330, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h341 | h341
          · linarith only [h0, h1, h341, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h343 | h343
            · linarith only [h0, h297, h343, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
              · linarith only [h0, h1, h325, h345, hlam, hphi, u0ehi6, u0elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h347 | h347
                · linarith only [h0, h1, h341, h347, hlam, hphi, u0ehi6, u0elo4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h350 | h350
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h351 | h351
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h352 | h352
                        · rcases h2bigk with h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h0, h1, h347, h349, h351, hc12, hc23, hlam, hphi, p353_1]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h297, hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h325, hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h341, hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h0, hlam, p353_1]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h343, hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h345, hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h347, hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p353_1, u0ehi6]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            rcases p353_3 (m.d 0 2) (by simp) with h365 | h365
                            · linarith only [h297, h365, hlam]
                            · linarith only [h0, h365, hlam]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h1, h347, h351, hc01, hc23, hlam, hphi, ht12, p353_1]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h0, h1, h347, hc23, hlam, hphi, ht01, ht12, p353_1, u0ehi6]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p353_1, u0ehi6]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            rcases p353_3 (m.d 0 2) (by simp) with h372 | h372
                            · linarith only [h325, h372, hlam]
                            · linarith only [h0, h372, hlam]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h349, hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h0, h1, h347, h349, hc23, hlam, hphi, ht01, ht12, p353_1, u0ehi6]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht12, p353_1, u0ehi6]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            rcases p353_3 (m.d 0 2) (by simp) with h379 | h379
                            · linarith only [h341, h379, hlam]
                            · linarith only [h0, h379, hlam]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h350, hlam, p353_0]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [h351, hlam, p353_1]
                          · have p353_0 := h353c.1
                            have p353_1 := h353c.2.1
                            have p353_2 := h353c.2.2.1
                            have p353_3 := h353c.2.2.2
                            linarith only [hlam, p353_0]
                        · rcases h2bigk with h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h297, hc12, hc23, hlam, hphi, p385_1]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h297, hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h325, hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h341, hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h0, hlam, p385_1]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h343, hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h345, hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h347, hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p385_1, u0ehi6]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            rcases p385_3 (m.d 0 2) (by simp) with h397 | h397
                            · linarith only [h297, h397, hlam]
                            · linarith only [h0, h397, hlam]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h1, h347, h351, hc01, hc23, hlam, hphi, ht12, p385_1]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h0, h1, h347, hc23, hlam, hphi, ht01, ht12, p385_1, u0ehi6]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p385_1, u0ehi6]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            rcases p385_3 (m.d 0 2) (by simp) with h404 | h404
                            · linarith only [h325, h404, hlam]
                            · linarith only [h0, h404, hlam]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h349, hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h0, h1, h347, h349, hc23, hlam, hphi, ht01, ht12, p385_1, u0ehi6]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht12, p385_1, u0ehi6]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            rcases p385_3 (m.d 0 2) (by simp) with h411 | h411
                            · linarith only [h341, h411, hlam]
                            · linarith only [h0, h411, hlam]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h350, hlam, p385_0]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [h351, hlam, p385_1]
                          · have p385_0 := h385c.1
                            have p385_1 := h385c.2.1
                            have p385_2 := h385c.2.2.1
                            have p385_3 := h385c.2.2.2
                            linarith only [hlam, p385_0]
                      · linarith only [h325, h351, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h297, h350, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h297, h349, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h420 | h420
    · rcases m.htr 0 2 3 (by decide) (by decide) with h421 | h421
      · rcases m.htr 0 2 4 (by decide) (by decide) with h422 | h422
        · rcases m.htr 0 2 5 (by decide) (by decide) with h423 | h423
          · rcases m.htr 1 2 3 (by decide) (by decide) with h424 | h424
            · rcases m.htr 1 2 4 (by decide) (by decide) with h425 | h425
              · rcases m.htr 1 2 5 (by decide) (by decide) with h426 | h426
                · rcases m.htr 2 3 4 (by decide) (by decide) with h427 | h427
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h428 | h428
                    · linarith only [h421, h428, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h430 | h430
                      · linarith only [h420, h426, h427, h428, h430, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h432 | h432
                        · linarith only [h0, h420, h426, h427, h428, h430, h432, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h2bigk with h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h427, hc34, hlam, hphi, ht0b, ht45, ht5b, p434_1, u0elo1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            rcases p434_3 (m.d 0 2) (by simp) with h438 | h438
                            · rcases p434_3 (m.d 1 2) (by simp) with h439 | h439
                              · rcases p434_3 (m.d 2 3) (by simp) with h440 | h440
                                · linarith only [h421, h440, hlam]
                                · linarith only [h427, h440, hlam]
                              · linarith only [h425, h439, hlam]
                            · linarith only [h438, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, hphi, ht0b, ht5b, p434_1, u0elo1, u5ehi2]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p434_1, u0ehi6]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            rcases p434_3 (m.d 0 2) (by simp) with h448 | h448
                            · linarith only [h0, h448, hlam]
                            · linarith only [h421, h448, hlam]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            rcases p434_3 (m.d 0 2) (by simp) with h451 | h451
                            · linarith only [h0, h451, hlam]
                            · linarith only [h422, h451, hlam]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            rcases p434_3 (m.d 0 2) (by simp) with h454 | h454
                            · linarith only [h0, h454, hlam]
                            · linarith only [h423, h454, hlam]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h421, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h424, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h428, h432, hc24, hc45, hlam, hphi, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h428, hlam, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h422, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h425, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h427, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h430, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h423, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h426, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h423, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p434_1, u0elo1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h420, h426, h427, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h472 | h472
                    · linarith only [h421, h472, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h474 | h474
                      · linarith only [h422, h474, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h476 | h476
                        · rcases h2bigk with h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h0, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            rcases p477_3 (m.d 0 2) (by simp) with h480 | h480
                            · rcases p477_3 (m.d 1 2) (by simp) with h481 | h481
                              · rcases p477_3 (m.d 2 3) (by simp) with h482 | h482
                                · linarith only [h482, hlam, p477_0]
                                · rcases p477_3 (m.d 2 4) (by simp) with h484 | h484
                                  · linarith only [h422, h484, hlam]
                                  · linarith only [h427, h484, hlam]
                              · linarith only [h424, h481, hlam]
                            · linarith only [h480, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            rcases p477_3 (m.d 0 2) (by simp) with h489 | h489
                            · rcases p477_3 (m.d 1 2) (by simp) with h490 | h490
                              · rcases p477_3 (m.d 2 3) (by simp) with h491 | h491
                                · linarith only [h421, h491, hlam]
                                · rcases p477_3 (m.d 2 4) (by simp) with h493 | h493
                                  · linarith only [h493, hlam, p477_0]
                                  · rcases p477_3 (m.d 2 5) (by simp) with h495 | h495
                                    · linarith only [h423, h495, hlam]
                                    · linarith only [h474, h495, hlam]
                              · linarith only [h425, h490, hlam]
                            · linarith only [h489, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [hlam, hphi, ht0b, ht5b, p477_1, u0elo1, u5ehi2]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p477_1, u0ehi6]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            rcases p477_3 (m.d 0 2) (by simp) with h503 | h503
                            · linarith only [h0, h503, hlam]
                            · linarith only [h421, h503, hlam]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            rcases p477_3 (m.d 0 2) (by simp) with h506 | h506
                            · linarith only [h0, h506, hlam]
                            · linarith only [h422, h506, hlam]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            rcases p477_3 (m.d 0 2) (by simp) with h509 | h509
                            · linarith only [h0, h509, hlam]
                            · linarith only [h423, h509, hlam]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h421, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h424, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h427, hlam, p477_1]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h472, hlam, p477_1]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h422, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h425, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h474, h476, hc23, hc34, hlam, hphi, p477_1]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h474, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h423, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h426, hlam, p477_0]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h423, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p477_1, u0elo1]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [h0, h420, h426, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p477_1]
                          · have p477_0 := h477c.1
                            have p477_1 := h477c.2.1
                            have p477_2 := h477c.2.2.1
                            have p477_3 := h477c.2.2.2
                            linarith only [hlam, p477_0]
                        · rcases h2bigk with h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h0, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            rcases p527_3 (m.d 0 2) (by simp) with h530 | h530
                            · rcases p527_3 (m.d 1 2) (by simp) with h531 | h531
                              · rcases p527_3 (m.d 2 3) (by simp) with h532 | h532
                                · linarith only [h532, hlam, p527_0]
                                · rcases p527_3 (m.d 2 4) (by simp) with h534 | h534
                                  · linarith only [h422, h534, hlam]
                                  · linarith only [h427, h534, hlam]
                              · linarith only [h424, h531, hlam]
                            · linarith only [h530, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            rcases p527_3 (m.d 0 2) (by simp) with h539 | h539
                            · rcases p527_3 (m.d 1 2) (by simp) with h540 | h540
                              · rcases p527_3 (m.d 2 3) (by simp) with h541 | h541
                                · linarith only [h421, h541, hlam]
                                · rcases p527_3 (m.d 2 4) (by simp) with h543 | h543
                                  · linarith only [h543, hlam, p527_0]
                                  · rcases p527_3 (m.d 2 5) (by simp) with h545 | h545
                                    · linarith only [h423, h545, hlam]
                                    · linarith only [h474, h545, hlam]
                              · linarith only [h425, h540, hlam]
                            · linarith only [h539, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [hlam, hphi, ht0b, ht5b, p527_1, u0elo1, u5ehi2]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p527_1, u0ehi6]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            rcases p527_3 (m.d 0 2) (by simp) with h553 | h553
                            · linarith only [h0, h553, hlam]
                            · linarith only [h421, h553, hlam]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            rcases p527_3 (m.d 0 2) (by simp) with h556 | h556
                            · linarith only [h0, h556, hlam]
                            · linarith only [h422, h556, hlam]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            rcases p527_3 (m.d 0 2) (by simp) with h559 | h559
                            · linarith only [h0, h559, hlam]
                            · linarith only [h423, h559, hlam]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h421, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h424, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h427, hlam, p527_1]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h472, hlam, p527_1]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h422, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h425, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h422, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p527_1, u0elo1]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h474, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h423, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h426, hlam, p527_0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h423, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p527_1, u0elo1]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [h420, h426, hc24, hlam, hphi, ht0b, ht45, ht5b, p527_1, u0elo0]
                          · have p527_0 := h527c.1
                            have p527_1 := h527c.2.1
                            have p527_2 := h527c.2.2.1
                            have p527_3 := h527c.2.2.2
                            linarith only [hlam, p527_0]
                · linarith only [h0, h423, h426, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h420, h425, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h420, h424, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · linarith only [h0, h420, h423, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h581 | h581
          · rcases m.htr 1 2 3 (by decide) (by decide) with h582 | h582
            · rcases m.htr 1 2 4 (by decide) (by decide) with h583 | h583
              · linarith only [h422, h581, h583, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h420, h583, hc24, hlam, hphi, ht01, ht12, u0ehi9]
            · linarith only [h0, h420, h421, h582, hlam, hphi, u0ehi9, u0elo1]
          · linarith only [h0, h420, h581, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h588 | h588
        · rcases m.htr 0 2 5 (by decide) (by decide) with h589 | h589
          · rcases m.htr 1 2 3 (by decide) (by decide) with h590 | h590
            · linarith only [h421, h589, h590, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · linarith only [h0, h420, h590, hc23, hlam, hphi, ht01, ht12, u0ehi9]
          · linarith only [h0, h420, h589, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h594 | h594
          · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
            · linarith only [h0, h420, h421, h595, hc12, hlam, hphi, ht01, u0ehi9]
            · linarith only [h0, h420, h595, hc23, hlam, hphi, ht01, ht12, u0ehi9]
          · linarith only [h0, h420, h594, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h599 | h599
      · rcases m.htr 0 2 4 (by decide) (by decide) with h600 | h600
        · rcases m.htr 0 2 5 (by decide) (by decide) with h601 | h601
          · rcases m.htr 1 2 3 (by decide) (by decide) with h602 | h602
            · rcases m.htr 1 2 4 (by decide) (by decide) with h603 | h603
              · rcases m.htr 1 2 5 (by decide) (by decide) with h604 | h604
                · rcases m.htr 2 3 4 (by decide) (by decide) with h605 | h605
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h606 | h606
                    · linarith only [h599, h606, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h608 | h608
                      · linarith only [h601, h605, h606, h608, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h610 | h610
                        · linarith only [h601, h605, h606, h608, h610, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases h2bigk with h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h0, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h605, hc34, hlam, hphi, ht0b, ht45, ht5b, p612_1, u0elo1]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            rcases p612_3 (m.d 0 2) (by simp) with h616 | h616
                            · rcases p612_3 (m.d 1 2) (by simp) with h617 | h617
                              · rcases p612_3 (m.d 2 3) (by simp) with h618 | h618
                                · linarith only [h599, h618, hlam]
                                · linarith only [h605, h618, hlam]
                              · linarith only [h603, h617, hlam]
                            · linarith only [h616, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [hlam, hphi, ht0b, ht5b, p612_1, u0elo1, u5ehi2]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p612_1, u0ehi6]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            rcases p612_3 (m.d 0 2) (by simp) with h626 | h626
                            · linarith only [h0, h626, hlam]
                            · linarith only [h599, h626, hlam]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            rcases p612_3 (m.d 0 2) (by simp) with h629 | h629
                            · linarith only [h0, h629, hlam]
                            · linarith only [h600, h629, hlam]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            rcases p612_3 (m.d 0 2) (by simp) with h632 | h632
                            · linarith only [h0, h632, hlam]
                            · linarith only [h601, h632, hlam]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h599, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h602, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h605, h606, h610, hc34, hc45, hlam, hphi, p612_1]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h606, hlam, p612_1]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h600, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h603, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h605, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h608, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h601, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h604, hlam, p612_0]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h601, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p612_1, u0elo1]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [h601, h605, hc34, hlam, hphi, ht0b, ht45, ht5b, p612_1, u0elo1]
                          · have p612_0 := h612c.1
                            have p612_1 := h612c.2.1
                            have p612_2 := h612c.2.2.1
                            have p612_3 := h612c.2.2.2
                            linarith only [hlam, p612_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h650 | h650
                    · linarith only [h599, h650, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h652 | h652
                      · linarith only [h600, h652, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h654 | h654
                        · rcases h2bigk with h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h0, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            rcases p655_3 (m.d 0 2) (by simp) with h658 | h658
                            · rcases p655_3 (m.d 1 2) (by simp) with h659 | h659
                              · rcases p655_3 (m.d 2 3) (by simp) with h660 | h660
                                · linarith only [h660, hlam, p655_0]
                                · rcases p655_3 (m.d 2 4) (by simp) with h662 | h662
                                  · linarith only [h600, h662, hlam]
                                  · linarith only [h605, h662, hlam]
                              · linarith only [h602, h659, hlam]
                            · linarith only [h658, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            rcases p655_3 (m.d 0 2) (by simp) with h667 | h667
                            · rcases p655_3 (m.d 1 2) (by simp) with h668 | h668
                              · rcases p655_3 (m.d 2 3) (by simp) with h669 | h669
                                · linarith only [h599, h669, hlam]
                                · rcases p655_3 (m.d 2 4) (by simp) with h671 | h671
                                  · linarith only [h671, hlam, p655_0]
                                  · rcases p655_3 (m.d 2 5) (by simp) with h673 | h673
                                    · linarith only [h601, h673, hlam]
                                    · linarith only [h652, h673, hlam]
                              · linarith only [h603, h668, hlam]
                            · linarith only [h667, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [hlam, hphi, ht0b, ht5b, p655_1, u0elo1, u5ehi2]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p655_1, u0ehi6]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            rcases p655_3 (m.d 0 2) (by simp) with h681 | h681
                            · linarith only [h0, h681, hlam]
                            · linarith only [h599, h681, hlam]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            rcases p655_3 (m.d 0 2) (by simp) with h684 | h684
                            · linarith only [h0, h684, hlam]
                            · linarith only [h600, h684, hlam]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            rcases p655_3 (m.d 0 2) (by simp) with h687 | h687
                            · linarith only [h0, h687, hlam]
                            · linarith only [h601, h687, hlam]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h599, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h602, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h605, hlam, p655_1]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h650, hlam, p655_1]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h600, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h603, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h600, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1, u0elo1]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h652, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h601, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h604, hlam, p655_0]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h601, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1, u0elo1]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [h601, hc24, hlam, hphi, ht0b, ht45, ht5b, p655_1, u0elo1]
                          · have p655_0 := h655c.1
                            have p655_1 := h655c.2.1
                            have p655_2 := h655c.2.2.1
                            have p655_3 := h655c.2.2.2
                            linarith only [hlam, p655_0]
                        · rcases h2bigk with h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h0, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            rcases p705_3 (m.d 0 2) (by simp) with h708 | h708
                            · rcases p705_3 (m.d 1 2) (by simp) with h709 | h709
                              · rcases p705_3 (m.d 2 3) (by simp) with h710 | h710
                                · linarith only [h710, hlam, p705_0]
                                · rcases p705_3 (m.d 2 4) (by simp) with h712 | h712
                                  · linarith only [h600, h712, hlam]
                                  · linarith only [h605, h712, hlam]
                              · linarith only [h602, h709, hlam]
                            · linarith only [h708, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            rcases p705_3 (m.d 0 2) (by simp) with h717 | h717
                            · rcases p705_3 (m.d 1 2) (by simp) with h718 | h718
                              · rcases p705_3 (m.d 2 3) (by simp) with h719 | h719
                                · linarith only [h599, h719, hlam]
                                · rcases p705_3 (m.d 2 4) (by simp) with h721 | h721
                                  · linarith only [h721, hlam, p705_0]
                                  · rcases p705_3 (m.d 2 5) (by simp) with h723 | h723
                                    · linarith only [h601, h723, hlam]
                                    · linarith only [h652, h723, hlam]
                              · linarith only [h603, h718, hlam]
                            · linarith only [h717, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [hlam, hphi, ht0b, ht5b, p705_1, u0elo1, u5ehi2]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p705_1, u0ehi6]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            rcases p705_3 (m.d 0 2) (by simp) with h731 | h731
                            · linarith only [h0, h731, hlam]
                            · linarith only [h599, h731, hlam]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            rcases p705_3 (m.d 0 2) (by simp) with h734 | h734
                            · linarith only [h0, h734, hlam]
                            · linarith only [h600, h734, hlam]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            rcases p705_3 (m.d 0 2) (by simp) with h737 | h737
                            · linarith only [h0, h737, hlam]
                            · linarith only [h601, h737, hlam]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h599, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h602, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h605, hlam, p705_1]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h650, hlam, p705_1]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h600, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h603, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h600, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p705_1, u0elo1]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h652, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h601, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h604, hlam, p705_0]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h601, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p705_1, u0elo1]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [h601, hc24, hlam, hphi, ht0b, ht45, ht5b, p705_1, u0elo1]
                          · have p705_0 := h705c.1
                            have p705_1 := h705c.2.1
                            have p705_2 := h705c.2.2.1
                            have p705_3 := h705c.2.2.2
                            linarith only [hlam, p705_0]
                · linarith only [h0, h601, h604, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h603, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h602, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h758 | h758
            · rcases m.htr 1 2 4 (by decide) (by decide) with h759 | h759
              · rcases m.htr 1 2 5 (by decide) (by decide) with h760 | h760
                · linarith only [h601, h760, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h760, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h600, h759, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h758, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h765 | h765
          · rcases m.htr 1 2 3 (by decide) (by decide) with h766 | h766
            · rcases m.htr 1 2 4 (by decide) (by decide) with h767 | h767
              · linarith only [h600, h765, h767, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h767, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h599, h766, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h771 | h771
            · rcases m.htr 1 2 4 (by decide) (by decide) with h772 | h772
              · linarith only [h600, h772, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h772, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h771, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h776 | h776
        · rcases m.htr 0 2 5 (by decide) (by decide) with h777 | h777
          · rcases m.htr 1 2 3 (by decide) (by decide) with h778 | h778
            · linarith only [h420, h599, h777, h778, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h778, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h781 | h781
            · linarith only [h599, h781, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h781, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h784 | h784
          · rcases m.htr 1 2 3 (by decide) (by decide) with h785 | h785
            · linarith only [h420, h599, h784, h785, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h785, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
            · linarith only [h599, h788, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h788, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
