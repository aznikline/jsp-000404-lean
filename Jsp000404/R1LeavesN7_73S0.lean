import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_0_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h10, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h10, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · linarith only [h1, h4, h7, h9, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                  · linarith only [h1, h3, h4, h7, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h7, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                      · linarith only [h18, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h15, h20, h5, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                            · rcases h5bigk with h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h1, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p24_1, u2elo0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h1, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p24_1, u2elo0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h1, h15, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p24_1, u2elo0, u3ehi1]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p24_1, u2elo0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h0, hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p24_1]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h15, hlam, p24_1]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p24_1]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h2, hlam, p24_1]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h6, hlam, p24_1]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h20, hlam, p24_1]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p24_1, u2elo4]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h3, hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h1, h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p24_1, u2elo0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h1, h3, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p24_1, u2elo0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h1, h3, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p24_1, u2elo0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h4, hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h17, hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h22, hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [h23, hlam, p24_0]
                              · have p24_0 := h24c.1
                                have p24_1 := h24c.2.1
                                have p24_2 := h24c.2.2.1
                                have p24_3 := h24c.2.2.2
                                linarith only [hlam, p24_0]
                            · linarith only [h1, h23, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                          · linarith only [h1, h18, h22, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                    · linarith only [h1, h17, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
              · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h54 | h54
              · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
                        · linarith only [h5, h54, h59, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                        · linarith only [h0, h5, h54, h56, h59, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h5, h54, h56, h58, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1, h4, h55, h57, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                  · linarith only [h1, h3, h4, h55, h56, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h55, h65, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h5, h54, h65, hlam]
              · linarith only [h2, h54, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
            · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                · rcases m.htr 1 3 5 (by decide) (by decide) with h72 | h72
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                    · linarith only [h0, h4, h73, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                      · linarith only [h69, h75, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h69, h71, h75, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                  · linarith only [h71, h72, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                  · linarith only [h71, h79, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                    · linarith only [h3, h4, h69, h71, h79, h81, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                      · linarith only [h69, h79, h83, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h79, h85, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                          · linarith only [h1, h81, h87, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                            · linarith only [h3, h4, h69, h79, h89, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h69, h71, h89, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h2, h70, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
              · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                    · linarith only [h0, h4, h96, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
                        · linarith only [h69, h93, h99, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                        · linarith only [h3, h69, h93, h99, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h69, h93, h94, h96, h98, hlam]
                  · linarith only [h94, h95, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h94, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h104, h69, h93, hlam]
              · linarith only [h2, h93, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
          · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
            · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
              · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
                  · linarith only [h109, h112, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                  · linarith only [h111, h112, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                  · linarith only [h111, h115, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                      · linarith only [h111, h118, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                        · linarith only [h109, h115, h120, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h122 | h122
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                            · rcases h5bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h109, h115, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1, u3ehi2]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p124_1, u2elo0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h3, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h1, h108, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p124_1, u2elo0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h115, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, h1, h108, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p124_1, u2elo0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h2, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h110, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h120, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p124_1, u2elo4]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h123, h3, hc34, hlam, hphi, p124_1, u3ehi0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h115, h123, hc34, hlam, hphi, p124_1, u3ehi1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h120, h123, hc34, hlam, hphi, p124_1, u3ehi2]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                rcases p124_3 (m.d 0 5) (by simp) with h144 | h144
                                · linarith only [h144, h3, hlam]
                                · linarith only [h108, h144, hlam]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h108, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h117, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h122, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h123, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                            · linarith only [h1, h108, h123, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                          · linarith only [h1, h108, h118, h122, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                    · linarith only [h1, h108, h109, h111, h117, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
              · linarith only [h110, h2, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
              · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                  · linarith only [h109, h158, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · linarith only [h157, h158, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h161 | h161
                  · linarith only [h157, h161, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h109, h156, h161, hlam]
              · linarith only [h156, h2, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
            · rcases m.htr 1 2 5 (by decide) (by decide) with h166 | h166
              · rcases m.htr 1 3 4 (by decide) (by decide) with h167 | h167
                · rcases m.htr 1 3 5 (by decide) (by decide) with h168 | h168
                  · linarith only [h165, h168, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                  · linarith only [h167, h168, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                  · linarith only [h167, h171, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h0, h108, h173, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                      · linarith only [h165, h171, h175, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                        · linarith only [h1, h175, h177, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                          · linarith only [h1, h167, h173, h179, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
                            · linarith only [h165, h167, h173, h181, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h165, h167, h181, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h166, h2, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
              · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                  · linarith only [h165, h187, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · linarith only [h186, h187, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h190 | h190
                  · linarith only [h186, h190, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h165, h185, h190, hlam]
              · linarith only [h185, h2, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h194 | h194
        · rcases m.htr 0 4 5 (by decide) (by decide) with h195 | h195
          · linarith only [h1, h195, h2, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
            · rcases m.htr 1 2 5 (by decide) (by decide) with h198 | h198
              · linarith only [h198, h2, hc02, hlam, hphi, u2elo1]
              · linarith only [h197, h198, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
              · linarith only [h1, h197, h2, h201, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
                · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                    · linarith only [h0, h195, h205, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                      · linarith only [h1, h2, h207, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
                      · linarith only [h197, h203, h207, hlam]
                  · linarith only [h194, h203, h204, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h211 | h211
                  · linarith only [h203, h211, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h213 | h213
                    · linarith only [h194, h195, h203, h211, h213, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
                      · linarith only [h203, h215, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · linarith only [h1, h197, h215, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h218 | h218
          · linarith only [h1, h2, h218, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
            · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
              · linarith only [h1, h2, h221, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h220, h221, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
              · linarith only [h1, h2, h220, h224, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h226 | h226
                · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
                  · linarith only [h194, h220, h227, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · linarith only [h226, h227, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                  · linarith only [h226, h230, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
                    · linarith only [h0, h218, h232, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                      · linarith only [h226, h234, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · linarith only [h1, h220, h234, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h237 | h237
      · rcases m.htr 0 3 5 (by decide) (by decide) with h238 | h238
        · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
          · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
            · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
              · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
                · rcases m.htr 1 3 5 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                      · linarith only [h240, h245, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h240, h242, h245, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · linarith only [h1, h239, h242, h244, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                  · linarith only [h1, h237, h238, h243, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h250 | h250
                  · linarith only [h242, h250, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1, h237, h238, h250, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
              · linarith only [h1, h237, h241, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
              · rcases m.htr 1 3 4 (by decide) (by decide) with h255 | h255
                · rcases m.htr 1 3 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                        · linarith only [h1, h237, h258, h259, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                        · linarith only [h0, h1, h237, h256, h258, h259, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h240, h254, h255, h258, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h1, h237, h239, h255, h257, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                  · linarith only [h1, h237, h238, h256, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
                  · linarith only [h255, h265, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1, h237, h238, h265, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
              · linarith only [h1, h237, h254, hc12, hlam, hphi, u2elo3]
          · linarith only [h1, h237, h239, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
          · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
            · rcases m.htr 1 2 5 (by decide) (by decide) with h272 | h272
              · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
                  · linarith only [h238, h271, h274, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                  · linarith only [h273, h274, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h277 | h277
                  · linarith only [h273, h277, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h279 | h279
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                      · linarith only [h271, h280, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h271, h277, h282, hlam]
                        · linarith only [h1, h237, h282, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
                    · linarith only [h1, h237, h270, h273, h279, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
              · linarith only [h1, h237, h272, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
              · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
                · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
                  · linarith only [h238, h271, h289, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · linarith only [h288, h289, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h292 | h292
                  · linarith only [h288, h292, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h271, h287, h292, hlam]
              · linarith only [h1, h237, h287, hc12, hlam, hphi, u2elo3]
          · linarith only [h1, h237, h270, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h297 | h297
        · rcases m.htr 0 4 5 (by decide) (by decide) with h298 | h298
          · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
            · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
              · linarith only [h237, h300, hc02, hlam, hphi, u2elo1]
              · linarith only [h299, h300, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h303 | h303
              · linarith only [h237, h299, h303, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
                · rcases m.htr 1 3 5 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h310 | h310
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
                            · rcases h5bigk with h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h298, h306, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p312_1, u3ehi4]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h237, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h1, h298, h308, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p312_1, u2elo2, u3ehi4]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h1, h298, h308, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p312_1, u2elo2]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h303, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p312_1, u3ehi4]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h1, h298, h308, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p312_1, u2elo2]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h308, h310, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p312_1, u2elo2]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h308, h310, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p312_1, u2elo2]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h308, h310, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p312_1, u2elo2, u3ehi4]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h308, h310, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p312_1, u2elo2]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h297, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h306, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h309, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h297, hc03, hc45, hlam, hphi, ht0b, ht5b, p312_1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h298, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h307, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h310, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h311, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                            · linarith only [h1, h298, h308, h311, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                          · linarith only [h1, h298, h310, hlam]
                        · linarith only [h299, h306, h309, hlam]
                      · linarith only [h299, h306, h308, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1, h298, h305, h307, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                  · linarith only [h297, h305, h306, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h344 | h344
                  · linarith only [h305, h344, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h346 | h346
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h347 | h347
                      · linarith only [h305, h347, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h349 | h349
                        · linarith only [h347, h349, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h237, h297, h299, h349, hc12, hlam, hphi, u2elo4]
                    · linarith only [h1, h298, h305, h346, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
            · rcases m.htr 1 2 5 (by decide) (by decide) with h354 | h354
              · linarith only [h237, h354, hc02, hlam, hphi, u2elo1]
              · linarith only [h353, h354, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h357 | h357
              · linarith only [h237, h353, h357, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
                · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h361 | h361
                    · linarith only [h1, h298, h353, h359, h361, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h364 | h364
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h365 | h365
                          · linarith only [h359, h361, h363, h365, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                            · linarith only [h1, h365, h367, hc02, hc34, hlam, hphi, ht23]
                            · rcases h5bigk with h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h237, h364, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p369_1, u2elo2]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h237, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h237, h364, h367, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p369_1, u2elo2]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h298, hlam, p369_1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h0, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h357, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h367, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p369_1, u3ehi3]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h361, hlam, p369_1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h364, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p369_1, u2elo2]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h364, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p369_1, u2elo2]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h364, h367, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p369_1, u2elo2, u3ehi3]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h365, hlam, p369_1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h297, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h360, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h364, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h367, hlam, p369_1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h0, h360, h367, hc45, hlam, hphi, ht34, p369_1, u3ehi3]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h360, h367, hc45, hlam, hphi, ht34, p369_1, u3ehi3]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h237, hc02, hc45, hlam, hphi, ht23, ht34, p369_1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h367, hc45, hlam, hphi, ht34, p369_1, u3ehi3]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                        · linarith only [h353, h360, h364, hlam]
                      · linarith only [h353, h360, h363, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h237, h297, h359, h360, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h398 | h398
                  · linarith only [h359, h398, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h400 | h400
                    · linarith only [h297, h298, h359, h398, h400, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h402 | h402
                      · linarith only [h359, h402, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h404 | h404
                        · linarith only [h402, h404, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h237, h297, h353, h404, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h407 | h407
          · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
            · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
              · linarith only [h237, h409, hc02, hlam, hphi, u2elo1]
              · linarith only [h408, h409, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h412 | h412
              · linarith only [h237, h408, h412, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
                · rcases m.htr 1 3 5 (by decide) (by decide) with h415 | h415
                  · linarith only [h297, h408, h415, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · linarith only [h414, h415, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                  · linarith only [h414, h418, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                      · linarith only [h408, h414, h421, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h423 | h423
                        · linarith only [h418, h423, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h425 | h425
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h426 | h426
                            · rcases h5bigk with h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h418, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p427_1, u3ehi1]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h237, hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h297, hlam, p427_1]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h1, h407, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p427_1, u2elo3]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h0, hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h412, hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h418, hlam, p427_1]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p427_1]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p427_1, u2elo4]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p427_1, u2elo4]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h423, hlam, p427_1]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h425, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p427_1, u2elo3]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h0, h418, hc35, hlam, hphi, p427_1, u3ehi1]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h418, hc35, hlam, hphi, p427_1, u3ehi1]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h237, hc02, hc35, hlam, hphi, ht23, p427_1]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                rcases p427_3 (m.d 0 5) (by simp) with h447 | h447
                                · linarith only [h297, h447, hlam]
                                · linarith only [h407, h447, hlam]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h407, hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h420, hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h425, hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [h426, hlam, p427_0]
                              · have p427_0 := h427c.1
                                have p427_1 := h427c.2.1
                                have p427_2 := h427c.2.2.1
                                have p427_3 := h427c.2.2.2
                                linarith only [hlam, p427_0]
                            · linarith only [h1, h407, h426, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                          · linarith only [h0, h1, h237, h420, h425, hc02, hlam, hphi, u2elo4]
                    · linarith only [h1, h407, h414, h420, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
            · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
              · linarith only [h237, h459, hc02, hlam, hphi, u2elo1]
              · linarith only [h458, h459, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h462 | h462
              · linarith only [h237, h458, h462, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h464 | h464
                · rcases m.htr 1 3 5 (by decide) (by decide) with h465 | h465
                  · linarith only [h297, h458, h465, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · linarith only [h464, h465, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h468 | h468
                  · linarith only [h464, h468, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h470 | h470
                    · linarith only [h0, h407, h470, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h472 | h472
                      · linarith only [h464, h472, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h474 | h474
                        · linarith only [h468, h474, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h476 | h476
                          · linarith only [h1, h407, h476, hc02, hlam, hphi, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h478 | h478
                            · linarith only [h458, h472, h476, h478, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h464, h478, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h481 | h481
    · rcases m.htr 0 2 5 (by decide) (by decide) with h482 | h482
      · rcases m.htr 0 3 5 (by decide) (by decide) with h483 | h483
        · rcases m.htr 0 4 5 (by decide) (by decide) with h484 | h484
          · rcases m.htr 1 2 3 (by decide) (by decide) with h485 | h485
            · rcases m.htr 1 2 5 (by decide) (by decide) with h486 | h486
              · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
                · rcases m.htr 1 3 5 (by decide) (by decide) with h488 | h488
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                      · linarith only [h485, h490, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h485, h487, h490, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · linarith only [h481, h484, h487, h489, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                  · linarith only [h483, h487, h488, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                  · linarith only [h487, h495, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h483, h495, hlam]
              · linarith only [h482, h486, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h499 | h499
              · linarith only [h0, h485, h499, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h482, h499, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
            · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
              · rcases m.htr 1 3 4 (by decide) (by decide) with h504 | h504
                · rcases m.htr 1 3 5 (by decide) (by decide) with h505 | h505
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h506 | h506
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h507 | h507
                      · linarith only [h502, h507, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h502, h504, h507, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h510 | h510
                      · linarith only [h502, h510, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h502, h504, h510, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                  · linarith only [h504, h505, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h514 | h514
                  · linarith only [h504, h514, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h483, h514, hlam]
              · linarith only [h482, h503, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h518 | h518
              · linarith only [h0, h502, h518, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h482, h518, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h521 | h521
          · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
            · rcases m.htr 1 2 5 (by decide) (by decide) with h523 | h523
              · rcases m.htr 1 3 4 (by decide) (by decide) with h524 | h524
                · rcases m.htr 1 3 5 (by decide) (by decide) with h525 | h525
                  · linarith only [h483, h522, h525, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                  · linarith only [h524, h525, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h528 | h528
                  · linarith only [h524, h528, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h530 | h530
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h531 | h531
                      · linarith only [h524, h531, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h533 | h533
                        · linarith only [h481, h528, h531, h533, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h535 | h535
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h536 | h536
                            · rcases h5bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [hlam, p537_0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h0, hlam, p537_1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h482, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p537_1, u2elo0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h483, hlam, p537_1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h481, h521, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p537_1, u2elo0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h0, h530, hc01, hc14, hlam, hphi, p537_1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [hlam, p537_0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h523, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p537_1, u2elo1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h528, hlam, p537_1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h523, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p537_1, u2elo1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h482, hlam, p537_1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h523, hlam, p537_1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [hlam, p537_0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h533, hlam, p537_1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p537_1, u2elo4]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p537_1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p537_1]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h533, hc35, hlam, hphi, p537_1, u3ehi2]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [hlam, p537_0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                rcases p537_3 (m.d 0 5) (by simp) with h557 | h557
                                · linarith only [h483, h557, hlam]
                                · linarith only [h521, h557, hlam]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h521, hlam, p537_0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h530, hlam, p537_0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h535, hlam, p537_0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [h536, hlam, p537_0]
                              · have p537_0 := h537c.1
                                have p537_1 := h537c.2.1
                                have p537_2 := h537c.2.2.1
                                have p537_3 := h537c.2.2.2
                                linarith only [hlam, p537_0]
                            · linarith only [h481, h521, h536, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                          · linarith only [h481, h521, h531, h535, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                    · linarith only [h481, h521, h522, h524, h530, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
              · linarith only [h482, h523, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
              · linarith only [h0, h522, h569, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h482, h569, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h572 | h572
            · rcases m.htr 1 2 5 (by decide) (by decide) with h573 | h573
              · rcases m.htr 1 3 4 (by decide) (by decide) with h574 | h574
                · rcases m.htr 1 3 5 (by decide) (by decide) with h575 | h575
                  · linarith only [h483, h572, h575, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                  · linarith only [h574, h575, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h578 | h578
                  · linarith only [h574, h578, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h580 | h580
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h581 | h581
                      · linarith only [h521, h574, h580, h581, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h481, h521, h574, h580, h581, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h584 | h584
                      · linarith only [h572, h584, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h586 | h586
                        · linarith only [h578, h586, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h588 | h588
                          · linarith only [h481, h580, h588, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h590 | h590
                            · linarith only [h481, h521, h584, h590, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h572, h574, h590, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h482, h573, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h594 | h594
              · linarith only [h0, h572, h594, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h482, h594, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h597 | h597
        · rcases m.htr 0 4 5 (by decide) (by decide) with h598 | h598
          · linarith only [h481, h482, h598, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h600 | h600
            · rcases m.htr 1 2 5 (by decide) (by decide) with h601 | h601
              · linarith only [h482, h601, hc02, hlam, hphi, u2elo1]
              · linarith only [h600, h601, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h604 | h604
              · linarith only [h481, h482, h600, h604, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h606 | h606
                · rcases m.htr 1 3 5 (by decide) (by decide) with h607 | h607
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h608 | h608
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h609 | h609
                      · linarith only [h481, h598, h600, h606, h608, h609, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                      · linarith only [h597, h598, h600, h606, h608, h609, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h612 | h612
                      · linarith only [h481, h482, h612, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
                      · linarith only [h600, h606, h612, hlam]
                  · linarith only [h606, h607, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h616 | h616
                  · linarith only [h606, h616, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h597, h616, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h619 | h619
          · linarith only [h481, h482, h619, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
            · rcases m.htr 1 2 5 (by decide) (by decide) with h622 | h622
              · linarith only [h482, h622, hc02, hlam, hphi, u2elo1]
              · linarith only [h621, h622, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
              · linarith only [h481, h482, h621, h625, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h627 | h627
                · rcases m.htr 1 3 5 (by decide) (by decide) with h628 | h628
                  · linarith only [h597, h621, h628, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · linarith only [h627, h628, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h631 | h631
                  · linarith only [h627, h631, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h633 | h633
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                      · linarith only [h627, h634, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · linarith only [h481, h482, h634, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h637 | h637
                      · linarith only [h627, h637, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · linarith only [h481, h621, h637, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h640 | h640
      · rcases m.htr 0 3 5 (by decide) (by decide) with h641 | h641
        · rcases m.htr 0 4 5 (by decide) (by decide) with h642 | h642
          · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
            · rcases m.htr 1 2 5 (by decide) (by decide) with h644 | h644
              · rcases m.htr 1 3 4 (by decide) (by decide) with h645 | h645
                · rcases m.htr 1 3 5 (by decide) (by decide) with h646 | h646
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h647 | h647
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h648 | h648
                      · linarith only [h643, h648, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h643, h645, h648, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · linarith only [h481, h640, h642, h645, h647, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                  · linarith only [h481, h640, h641, h646, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h653 | h653
                  · linarith only [h645, h653, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h481, h640, h641, h653, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
              · linarith only [h481, h640, h644, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h657 | h657
              · linarith only [h0, h643, h657, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h481, h640, h657, hc12, hlam, hphi, u2elo3]
          · linarith only [h481, h640, h642, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h661 | h661
          · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
            · rcases m.htr 1 2 5 (by decide) (by decide) with h663 | h663
              · rcases m.htr 1 3 4 (by decide) (by decide) with h664 | h664
                · rcases m.htr 1 3 5 (by decide) (by decide) with h665 | h665
                  · linarith only [h641, h662, h665, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                  · linarith only [h664, h665, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h668 | h668
                  · linarith only [h664, h668, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h670 | h670
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h671 | h671
                      · linarith only [h664, h671, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h673 | h673
                        · linarith only [h662, h668, h673, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
                        · linarith only [h481, h640, h673, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
                    · linarith only [h481, h661, h662, h664, h670, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h481, h640, h663, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h678 | h678
              · linarith only [h0, h662, h678, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h481, h640, h678, hc12, hlam, hphi, u2elo3]
          · linarith only [h481, h640, h661, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h682 | h682
        · rcases m.htr 0 4 5 (by decide) (by decide) with h683 | h683
          · rcases m.htr 1 2 3 (by decide) (by decide) with h684 | h684
            · rcases m.htr 1 2 5 (by decide) (by decide) with h685 | h685
              · linarith only [h640, h685, hc02, hlam, hphi, u2elo1]
              · linarith only [h684, h685, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h688 | h688
              · linarith only [h640, h684, h688, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h690 | h690
                · rcases m.htr 1 3 5 (by decide) (by decide) with h691 | h691
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h692 | h692
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h693 | h693
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h694 | h694
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h695 | h695
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h696 | h696
                            · rcases h5bigk with h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h0, hlam, p697_1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h640, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h683, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p697_1, u3ehi4]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h640, h693, h695, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p697_1, u2elo2]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h0, h692, hc01, hc14, hlam, hphi, p697_1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h688, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h691, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p697_1, u3ehi4]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h688, h693, h695, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p697_1, u2elo2]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h682, h693, h695, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p697_1, u2elo2, u3ehi4]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h693, h695, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p697_1, u2elo2]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h693, h695, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p697_1, u2elo2, u3ehi4]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h693, h695, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p697_1, u2elo2]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h682, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h691, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h694, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h682, hc03, hc45, hlam, hphi, ht0b, ht5b, p697_1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h683, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h692, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h695, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h696, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                            · linarith only [h481, h683, h693, h696, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                          · linarith only [h481, h683, h695, hlam]
                        · linarith only [h684, h691, h694, hlam]
                      · linarith only [h684, h691, h693, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h481, h683, h690, h692, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                  · linarith only [h0, h682, h688, h690, h691, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h729 | h729
                  · linarith only [h690, h729, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h682, h729, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h732 | h732
            · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
              · linarith only [h640, h733, hc02, hlam, hphi, u2elo1]
              · linarith only [h732, h733, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h736 | h736
              · linarith only [h640, h732, h736, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h738 | h738
                · rcases m.htr 1 3 5 (by decide) (by decide) with h739 | h739
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h740 | h740
                    · linarith only [h481, h683, h732, h738, h740, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h743 | h743
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h744 | h744
                          · linarith only [h738, h740, h742, h744, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h746 | h746
                            · linarith only [h481, h683, h732, h738, h746, hc02, hlam, hphi, u2elo2]
                            · rcases h5bigk with h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [hlam, p748_0]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h0, hlam, p748_1]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h640, hlam, p748_0]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h0, h736, h746, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p748_1, u2elo4]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h683, hlam, p748_1]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h736, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p748_1, u2elo4]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [hlam, p748_0]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h736, hlam, p748_0]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h732, h739, h746, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p748_1, u2elo2, u3ehi3]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h740, hlam, p748_1]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h682, h746, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p748_1, u2elo4, u3ehi3]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p748_1, u2elo4]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [hlam, p748_0]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h743, h746, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p748_1, u2elo2, u3ehi3]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h744, hlam, p748_1]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h682, hlam, p748_0]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h739, hlam, p748_0]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h743, hlam, p748_0]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [hlam, p748_0]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h746, hlam, p748_1]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h682, h746, hc45, hlam, hphi, ht34, p748_1, u3ehi3]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p748_1]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h732, h736, h739, h746, hc12, hc45, hlam, hphi, ht34, p748_1, u2elo2, u3ehi3]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [h746, hc45, hlam, hphi, ht34, p748_1, u3ehi3]
                              · have p748_0 := h748c.1
                                have p748_1 := h748c.2.1
                                have p748_2 := h748c.2.2.1
                                have p748_3 := h748c.2.2.2
                                linarith only [hlam, p748_0]
                        · linarith only [h732, h739, h743, hlam]
                      · linarith only [h732, h739, h742, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h738, h739, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h777 | h777
                  · linarith only [h738, h777, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h682, h777, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h780 | h780
          · rcases m.htr 1 2 3 (by decide) (by decide) with h781 | h781
            · rcases m.htr 1 2 5 (by decide) (by decide) with h782 | h782
              · linarith only [h640, h782, hc02, hlam, hphi, u2elo1]
              · linarith only [h781, h782, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h785 | h785
              · linarith only [h640, h781, h785, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h787 | h787
                · rcases m.htr 1 3 5 (by decide) (by decide) with h788 | h788
                  · linarith only [h682, h781, h788, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · linarith only [h787, h788, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h791 | h791
                  · linarith only [h787, h791, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h793 | h793
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h794 | h794
                      · linarith only [h787, h794, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h796 | h796
                        · linarith only [h781, h791, h794, h796, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h798 | h798
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h799 | h799
                            · rcases h5bigk with h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h0, hlam, p800_1]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h640, hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h682, hlam, p800_1]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h0, h785, h798, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p800_1, u2elo3]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h785, h798, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p800_1, u2elo3]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h785, hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h791, hlam, p800_1]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h785, h798, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p800_1, u2elo3]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h682, h798, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p800_1, u2elo3, u3ehi0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h798, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p800_1, u2elo3]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h796, hlam, p800_1]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h798, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p800_1, u2elo3]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h682, hc35, hlam, hphi, p800_1, u3ehi0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p800_1]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h640, hc02, hc35, hlam, hphi, ht23, p800_1]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                rcases p800_3 (m.d 0 5) (by simp) with h820 | h820
                                · linarith only [h682, h820, hlam]
                                · linarith only [h780, h820, hlam]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h780, hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h793, hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h798, hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [h799, hlam, p800_0]
                              · have p800_0 := h800c.1
                                have p800_1 := h800c.2.1
                                have p800_2 := h800c.2.2.1
                                have p800_3 := h800c.2.2.2
                                linarith only [hlam, p800_0]
                            · linarith only [h481, h780, h799, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                          · linarith only [h0, h481, h780, h785, h798, hc02, hlam, hphi, u2elo4]
                    · linarith only [h481, h780, h787, h793, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h831 | h831
            · rcases m.htr 1 2 5 (by decide) (by decide) with h832 | h832
              · linarith only [h640, h832, hc02, hlam, hphi, u2elo1]
              · linarith only [h831, h832, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h835 | h835
              · linarith only [h640, h831, h835, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h837 | h837
                · rcases m.htr 1 3 5 (by decide) (by decide) with h838 | h838
                  · linarith only [h682, h831, h838, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                  · linarith only [h837, h838, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                  · linarith only [h837, h841, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h843 | h843
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h844 | h844
                      · linarith only [h780, h837, h843, h844, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h846 | h846
                        · linarith only [h841, h846, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h848 | h848
                          · linarith only [h481, h780, h848, hc02, hlam, hphi, u2elo3]
                          · linarith only [h481, h835, h843, h848, hc02, hlam, hphi, u2elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h851 | h851
                      · linarith only [h837, h851, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h853 | h853
                        · linarith only [h851, h853, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h855 | h855
                          · linarith only [h481, h780, h855, hc02, hlam, hphi, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h857 | h857
                            · linarith only [h831, h851, h855, h857, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h837, h857, hc45, hlam, hphi, ht34, u3ehi1]

end R2N4
