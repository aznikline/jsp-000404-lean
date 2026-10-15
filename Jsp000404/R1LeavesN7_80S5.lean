import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_13_25_L_I_L_0_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h10, h11, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h10, h14, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                        · linarith only [h14, h5, hc23, hlam, hphi, u3elo0]
                    · linarith only [h5, h9, hc13, hlam, hphi, u3elo0]
                  · linarith only [h4, h6, h8, hc23, hlam, hphi, ht34, ht45, u5elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h19, h3, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · linarith only [h19, h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                  · linarith only [h23, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
                  · linarith only [h22, h23, h4, hc24, hlam, hphi, ht45, u5elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h22, h26, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                            · linarith only [h2, h29, h32, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi9]
                            · rcases h2bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                rcases p34_3 (m.d 0 2) (by simp) with h36 | h36
                                · rcases p34_3 (m.d 1 2) (by simp) with h37 | h37
                                  · linarith only [h0, h37, hlam]
                                  · rcases p34_3 (m.d 2 3) (by simp) with h39 | h39
                                    · linarith only [h2, h39, hlam]
                                    · linarith only [h39, h6, hlam]
                                · linarith only [h0, h36, hlam]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h0, h29, h31, h32, hc01, hlam, hphi, ht0b, ht5b, p34_1, u5ehi8]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h0, h31, h32, hc01, hlam, hphi, ht0b, ht5b, p34_1, u5ehi8]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                rcases p34_3 (m.d 0 2) (by simp) with h45 | h45
                                · rcases p34_3 (m.d 1 2) (by simp) with h46 | h46
                                  · linarith only [h0, h46, hlam]
                                  · rcases p34_3 (m.d 2 3) (by simp) with h48 | h48
                                    · linarith only [h2, h48, hlam]
                                    · linarith only [h30, h48, hlam]
                                · linarith only [h45, hlam, p34_0]
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
                                linarith only [h6, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h22, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h26, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h2, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h2, hc12, hlam, hphi, ht23, p34_1, u3elo0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h2, h31, h32, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p34_1, u3elo0, u5ehi8]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h2, h26, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p34_1, u3elo0, u5ehi6]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h3, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h2, h29, hc12, hlam, hphi, ht23, p34_1, u3elo0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h29, hlam, p34_1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h2, h26, h29, hc12, hlam, hphi, ht23, p34_1, u3elo0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h4, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p34_1, u5elo2]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h30, hlam, p34_1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h31, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                          · linarith only [h2, h22, h28, h31, h6, hc12, hlam, hphi, ht23, u3elo0, u5ehi8, u5elo4]
                        · linarith only [h28, h30, h6, hlam]
                      · linarith only [h28, h29, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                    · linarith only [h28, h5, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
              · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                    · linarith only [h1, h5, h79, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                      · linarith only [h1, h5, h76, h81, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                        · linarith only [h1, h5, h76, h83, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                          · linarith only [h0, h77, h85, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                            · linarith only [h81, h85, h87, hc23, hlam, hphi, u3elo3]
                            · linarith only [h81, h87, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h4, h76, h78, hc23, hlam, hphi, ht34, ht45, u5elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
                  · linarith only [h0, h3, h77, h91, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · linarith only [h4, h5, h76, h91, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h2, h5, h76, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h3, h4, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h96 | h96
          · rcases m.htr 0 3 5 (by decide) (by decide) with h97 | h97
            · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
              · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
                · linarith only [h0, h3, h99, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                      · linarith only [h0, h103, h3, h98, hlam]
                      · linarith only [h0, h103, h3, h98, hc23, hlam, hphi, u3elo3]
                    · linarith only [h102, h97, hc13, hlam, hphi, u3elo0]
                  · linarith only [h101, h3, h96, hc12, hc24, hlam, hphi]
              · linarith only [h2, h3, h98, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
              · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                · linarith only [h110, h3, h96, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                    · linarith only [h1, h113, h97, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                      · linarith only [h1, h109, h115, h97, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h0, h112, h115, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi7]
                  · linarith only [h112, h3, h96, hc12, hc24, hlam, hphi]
              · linarith only [h109, h2, h3, hc12, hc24, hlam, hphi]
          · linarith only [h2, h96, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h121 | h121
        · rcases m.htr 0 2 5 (by decide) (by decide) with h122 | h122
          · linarith only [h122, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
          · linarith only [h121, h122, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h125 | h125
          · linarith only [h125, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h127 | h127
            · rcases m.htr 1 2 3 (by decide) (by decide) with h128 | h128
              · linarith only [h0, h125, h128, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
                · linarith only [h121, h128, h130, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                  · linarith only [h0, h132, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h135, h138, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi9]
                            · rcases h2bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h125, hc12, hlam, hphi, ht23, ht34, ht45, p140_1, u5elo2]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h2, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h121, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h125, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h0, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h128, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h130, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h132, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hc02, hlam, hphi, ht23, p140_1, u3elo2]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, p140_1, u3elo2]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h137, h138, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p140_1, u3elo2]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p140_1, u3elo2, u5ehi7]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h0, h135, hc12, hlam, hphi, ht23, p140_1, u3elo2]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h135, hc12, hlam, hphi, ht23, p140_1, u3elo2]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h135, hlam, p140_1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h0, h125, h135, hc12, hlam, hphi, ht23, p140_1, u3elo2]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p140_1, u5elo2]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h1, h134, h2, hc12, hlam, hphi, ht23, p140_1, u3elo2, u5ehi8, u5elo2]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h136, hlam, p140_1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h137, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                          · linarith only [h0, h1, h121, h134, h137, h2, hc12, hlam, hphi, ht23, u3elo2, u5ehi8, u5elo4]
                        · linarith only [h1, h134, h136, h2, hlam]
                      · linarith only [h1, h134, h135, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                    · linarith only [h127, h134, h2, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
              · linarith only [h0, h170, h2, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                · linarith only [h0, h121, h127, h172, h2, hc04, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h0, h125, h127, h174, h2, hlam, hphi, u5ehi5, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h176 | h176
                    · linarith only [h127, h176, h2, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                        · linarith only [h0, h127, h179, h2, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h178, h179, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h0, h178, h2, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h184 | h184
    · rcases m.htr 0 2 3 (by decide) (by decide) with h185 | h185
      · rcases m.htr 0 2 4 (by decide) (by decide) with h186 | h186
        · rcases m.htr 0 2 5 (by decide) (by decide) with h187 | h187
          · rcases m.htr 0 3 5 (by decide) (by decide) with h188 | h188
            · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
              · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
                · rcases m.htr 1 2 5 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                    · linarith only [h0, h184, h192, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · linarith only [h188, h192, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h191, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h184, h186, h188, h190, hc02, hlam, hphi, ht0b, ht5b, u5ehi8]
              · linarith only [h0, h184, h188, h189, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi8]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
              · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
                · rcases m.htr 1 2 5 (by decide) (by decide) with h200 | h200
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h0, h184, h188, h201, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                      · linarith only [h184, h188, h198, h203, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                        · linarith only [h184, h188, h198, h205, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                            · rcases h2bigk with h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h0, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 2) (by simp) with h212 | h212
                                · rcases p209_3 (m.d 1 2) (by simp) with h213 | h213
                                  · rcases p209_3 (m.d 2 3) (by simp) with h214 | h214
                                    · linarith only [h214, hlam, p209_0]
                                    · rcases p209_3 (m.d 2 4) (by simp) with h216 | h216
                                      · linarith only [h186, h216, hlam]
                                      · linarith only [h203, h216, hlam]
                                  · linarith only [h198, h213, hlam]
                                · linarith only [h212, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h207, hc02, hlam, hphi, ht0b, ht5b, p209_1, u5ehi9]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 2) (by simp) with h222 | h222
                                · rcases p209_3 (m.d 1 2) (by simp) with h223 | h223
                                  · rcases p209_3 (m.d 2 3) (by simp) with h224 | h224
                                    · linarith only [h185, h224, hlam]
                                    · rcases p209_3 (m.d 2 4) (by simp) with h226 | h226
                                      · linarith only [h186, h226, hlam]
                                      · linarith only [h207, h226, hlam]
                                  · linarith only [h200, h223, hlam]
                                · linarith only [h222, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h186, h207, hc12, hlam, hphi, ht01, ht0b, ht5b, p209_1, u5ehi9]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 2) (by simp) with h233 | h233
                                · linarith only [h0, h233, hlam]
                                · linarith only [h185, h233, hlam]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h207, hc12, hlam, hphi, ht01, ht0b, ht5b, p209_1, u5ehi9]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 2) (by simp) with h237 | h237
                                · linarith only [h0, h237, hlam]
                                · linarith only [h187, h237, hlam]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h185, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h198, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h203, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h205, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h186, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h199, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h203, hc23, hlam, hphi, p209_1, u3elo3]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h203, h207, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p209_1, u3elo3, u5ehi9]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h187, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h200, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h200, hc23, hlam, hphi, ht34, ht45, p209_1, u5elo1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h207, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                            · linarith only [h203, h208, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h256 | h256
                            · linarith only [h203, h207, h256, hc23, hlam, hphi, u3elo3]
                            · linarith only [h203, h256, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h200, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h186, h199, hlam]
              · linarith only [h0, h198, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h0, h184, h187, hc13, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h263 | h263
          · rcases m.htr 0 3 5 (by decide) (by decide) with h264 | h264
            · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
              · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                · linarith only [h0, h184, h186, h264, h266, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · linarith only [h0, h184, h264, h266, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h0, h184, h264, h265, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
              · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
                · linarith only [h186, h263, h271, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h273 | h273
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
                    · linarith only [h0, h184, h264, h271, h274, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                      · linarith only [h0, h184, h270, h271, h276, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h271, h276, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h184, h263, h270, h273, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h263, h270, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
          · linarith only [h0, h184, h263, hc13, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h184, h185, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h283 | h283
      · rcases m.htr 0 2 4 (by decide) (by decide) with h284 | h284
        · rcases m.htr 0 2 5 (by decide) (by decide) with h285 | h285
          · rcases m.htr 0 3 5 (by decide) (by decide) with h286 | h286
            · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
              · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h290 | h290
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h294 | h294
                            · linarith only [h283, h291, h294, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h2bigk with h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h0, hlam, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h0, h291, h293, h294, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h0, h293, h294, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                rcases p296_3 (m.d 0 2) (by simp) with h301 | h301
                                · rcases p296_3 (m.d 1 2) (by simp) with h302 | h302
                                  · rcases p296_3 (m.d 2 3) (by simp) with h303 | h303
                                    · linarith only [h283, h303, hlam]
                                    · linarith only [h292, h303, hlam]
                                  · linarith only [h289, h302, hlam]
                                · linarith only [h301, hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h283, h291, h293, h294, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h291, h293, h294, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h293, h294, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                rcases p296_3 (m.d 0 2) (by simp) with h312 | h312
                                · linarith only [h0, h312, hlam]
                                · linarith only [h285, h312, hlam]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h283, hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h287, hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h283, h293, h294, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h184, h283, h293, h294, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p296_1, u3elo1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h284, hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h288, hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h291, hlam, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h0, h284, h293, h294, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h285, hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h289, hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h292, hlam, p296_1]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [h293, hlam, p296_0]
                              · have p296_0 := h296c.1
                                have p296_1 := h296c.2.1
                                have p296_2 := h296c.2.2.1
                                have p296_3 := h296c.2.2.2
                                linarith only [hlam, p296_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h330 | h330
                            · linarith only [h184, h283, h291, h293, h330, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases h2bigk with h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h0, hlam, p332_1]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h0, h292, hc12, hlam, hphi, ht01, ht0b, ht5b, p332_1, u5ehi8]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                rcases p332_3 (m.d 0 2) (by simp) with h336 | h336
                                · rcases p332_3 (m.d 1 2) (by simp) with h337 | h337
                                  · rcases p332_3 (m.d 2 3) (by simp) with h338 | h338
                                    · linarith only [h283, h338, hlam]
                                    · linarith only [h291, h338, hlam]
                                  · linarith only [h288, h337, hlam]
                                · linarith only [h336, hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                rcases p332_3 (m.d 0 2) (by simp) with h343 | h343
                                · rcases p332_3 (m.d 1 2) (by simp) with h344 | h344
                                  · rcases p332_3 (m.d 2 3) (by simp) with h345 | h345
                                    · linarith only [h283, h345, hlam]
                                    · linarith only [h292, h345, hlam]
                                  · linarith only [h289, h344, hlam]
                                · linarith only [h343, hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h283, h292, hc12, hlam, hphi, ht01, ht0b, ht5b, p332_1, u5ehi8]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h292, hc12, hlam, hphi, ht01, ht0b, ht5b, p332_1, u5ehi8]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                rcases p332_3 (m.d 0 2) (by simp) with h353 | h353
                                · linarith only [h0, h353, hlam]
                                · linarith only [h284, h353, hlam]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                rcases p332_3 (m.d 0 2) (by simp) with h356 | h356
                                · linarith only [h0, h356, hlam]
                                · linarith only [h285, h356, hlam]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h283, hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h287, hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                rcases p332_3 (m.d 0 2) (by simp) with h362 | h362
                                · rcases p332_3 (m.d 1 2) (by simp) with h363 | h363
                                  · rcases p332_3 (m.d 2 3) (by simp) with h364 | h364
                                    · rcases p332_3 (m.d 2 4) (by simp) with h365 | h365
                                      · linarith only [h291, h365, hlam]
                                      · rcases p332_3 (m.d 2 5) (by simp) with h367 | h367
                                        · linarith only [h292, h367, hlam]
                                        · linarith only [h293, h367, hlam]
                                    · linarith only [h291, h364, hlam]
                                  · linarith only [h288, h363, hlam]
                                · linarith only [h284, h362, hlam]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h283, hc02, hlam, hphi, ht0b, ht5b, p332_1, u5ehi7]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h284, hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h288, hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h291, hlam, p332_1]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h293, hlam, p332_1]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h285, hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h289, hlam, p332_0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h292, hlam, p332_1]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [h285, h291, hc34, hlam, hphi, ht45, p332_1, u5elo0]
                              · have p332_0 := h332c.1
                                have p332_1 := h332c.2.1
                                have p332_2 := h332c.2.2.1
                                have p332_3 := h332c.2.2.2
                                linarith only [hlam, p332_0]
                        · linarith only [h184, h286, h292, hc23, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
                        · linarith only [h291, h385, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                        · linarith only [h184, h286, h385, hc23, hlam, hphi, u3elo1]
                    · linarith only [h184, h286, h290, hlam]
                  · linarith only [h0, h285, h289, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h0, h284, h288, hlam]
              · linarith only [h0, h283, h286, h287, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi8]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h392 | h392
              · rcases m.htr 1 2 4 (by decide) (by decide) with h393 | h393
                · rcases m.htr 1 2 5 (by decide) (by decide) with h394 | h394
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h395 | h395
                    · linarith only [h286, h395, hc03, hlam, hphi, u3elo1]
                    · linarith only [h184, h395, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h285, h394, hlam]
                · linarith only [h0, h284, h393, hlam]
              · linarith only [h0, h285, h392, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
          · linarith only [h283, h285, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h402 | h402
          · rcases m.htr 0 3 5 (by decide) (by decide) with h403 | h403
            · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
              · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
                · linarith only [h283, h284, h403, h405, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h409 | h409
                      · linarith only [h0, h405, h409, hc01, hlam, hphi, ht12, ht23, u3elo2]
                      · linarith only [h0, h283, h403, h405, h409, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                    · linarith only [h184, h403, h408, hlam]
                  · linarith only [h0, h283, h403, h407, hlam, hphi, u5ehi8, u5elo2]
              · linarith only [h0, h283, h404, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
              · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
                · linarith only [h284, h402, h416, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h418 | h418
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h419 | h419
                    · linarith only [h403, h419, hc03, hlam, hphi, u3elo1]
                    · linarith only [h184, h419, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h418, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h283, h402, h415, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi7]
          · linarith only [h283, h402, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h425 | h425
        · rcases m.htr 0 2 5 (by decide) (by decide) with h426 | h426
          · linarith only [h283, h426, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
          · linarith only [h425, h426, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h429 | h429
          · linarith only [h283, h429, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h431 | h431
            · rcases m.htr 1 2 3 (by decide) (by decide) with h432 | h432
              · rcases m.htr 1 2 4 (by decide) (by decide) with h433 | h433
                · rcases m.htr 1 2 5 (by decide) (by decide) with h434 | h434
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h435 | h435
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h436 | h436
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h437 | h437
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h438 | h438
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h439 | h439
                            · linarith only [h432, h436, h439, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi9]
                            · rcases h2bigk with h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, hlam, p441_1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h283, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h425, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h429, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                rcases p441_3 (m.d 0 2) (by simp) with h447 | h447
                                · linarith only [h0, h447, hlam]
                                · rcases p441_3 (m.d 1 2) (by simp) with h449 | h449
                                  · rcases p441_3 (m.d 2 3) (by simp) with h450 | h450
                                    · linarith only [h432, h450, hlam]
                                    · linarith only [h283, h450, hlam]
                                  · linarith only [h0, h449, hlam]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h283, hc01, hc12, hlam, hphi, p441_1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h429, h434, h438, h439, hc01, hc12, hc34, hlam, hphi, ht45, p441_1, u5elo1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h429, hc01, hc12, hlam, hphi, p441_1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p441_1, u3elo2]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h432, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h429, h432, h434, h438, h439, hc01, hc34, hlam, hphi, ht12, ht23, ht45, p441_1, u3elo1, u5elo1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h429, h432, hc01, hlam, hphi, ht12, ht23, p441_1, u3elo1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h433, hc01, hc12, hlam, hphi, p441_1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h433, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h436, hlam, p441_1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h429, h432, h436, hc01, hlam, hphi, ht12, ht23, p441_1, u3elo1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h434, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p441_1, u5elo1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h434, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h437, hlam, p441_1]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h438, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                          · linarith only [h0, h283, h425, h431, h432, h438, hc01, hlam, hphi, ht12, ht23, u3elo1, u5ehi8, u5elo4]
                        · linarith only [h283, h431, h437, hlam]
                      · linarith only [h283, h431, h436, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                    · linarith only [h431, h435, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h283, h431, h432, h434, hc01, hlam, hphi, ht12, ht23, u3elo1, u5ehi8, u5elo2]
                · linarith only [h283, h431, h432, h433, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h0, h432, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h480 | h480
              · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
                · rcases m.htr 1 2 5 (by decide) (by decide) with h482 | h482
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h483 | h483
                    · linarith only [h431, h483, hc03, hlam, hphi, u3elo1]
                    · linarith only [h184, h483, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h283, h480, h482, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h283, h480, h481, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h480, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
