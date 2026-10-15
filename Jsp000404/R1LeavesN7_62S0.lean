import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3256000 in
theorem r1l7_11_13_25_L_0_L_0_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h15, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h15, h6, hc23, hlam, hphi, u3elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                              · linarith only [h0, h18, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h18, h6, hc23, hlam, hphi, u3elo0]
                          · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h12, h6, h9, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h11, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                        · linarith only [h10, h25, h9, hlam]
                        · linarith only [h25, h6, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h24, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h0, h29, h4, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                      · linarith only [h0, h31, h4, h9, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                                    · linarith only [h1, h33, h39, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h0, h33, h35, h39, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h33, h35, h38, h4, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h34, h37, h9, hlam]
                              · linarith only [h36, h6, h9, hc13, hlam, hphi, u3elo0]
                            · linarith only [h29, h35, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
                          · linarith only [h0, h33, h34, h4, h7, h9, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, u1elo0, u3elo0]
                        · linarith only [h33, h6, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                            · linarith only [h2, h53, h8, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                              · linarith only [h0, h48, h55, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h51, h55, hc23, hlam, hphi, u3elo1]
                          · linarith only [h52, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h48, h51, h6, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h48, h5, h50, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                        · linarith only [h48, h49, h62, hlam]
                        · linarith only [h6, h62, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h48, h5, h61, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
                    · linarith only [h0, h4, h48, h66, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
                      · linarith only [h0, h4, h48, h68, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h70 | h70
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                            · linarith only [h2, h72, h8, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                                  · linarith only [h0, h4, h74, h76, h8, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                                    · linarith only [h70, h76, h78, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
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
                                        linarith only [h66, h7, h72, hc12, hlam, hphi, ht23, p80_1, u3elo0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p80_1, u3elo0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h7, h78, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p80_1, u3elo0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h8, hlam, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h3, hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h68, hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h78, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p80_1, u1elo4]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h72, hlam, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h5, hlam, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p80_1, u1elo0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h0, h4, h75, h78, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p80_1, u1elo0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h76, hlam, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h7, hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h71, hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h75, hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h78, hlam, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h3, h66, h72, hc12, hc45, hlam, hphi, ht23, ht34, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h66, h72, hc12, hc45, hlam, hphi, ht23, ht34, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h68, hc12, hc45, hlam, hphi, ht23, ht34, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h78, hc34, hc45, hlam, hphi, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [hlam, p80_0]
                                · linarith only [h48, h7, h75, hc13, hlam, hphi, u3elo0]
                              · linarith only [h48, h70, h74, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h7, h71, hc13, hlam, hphi, u3elo0]
                        · linarith only [h48, h6, h70, hc12, hlam, hphi, ht23, u3elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h110 | h110
                · linarith only [h110, h6, h7, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                          · linarith only [h1, h116, h7, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
                            · linarith only [h110, h118, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                              · linarith only [h0, h112, h120, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h1, h115, h120, h7, hc23, hlam, hphi, u3elo4]
                        · linarith only [h115, h6, h7, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h113, h114, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h112, h113, h2, h6, h7, hc23, hlam, hphi, u3elo4]
                  · linarith only [h112, h4, h7, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h127 | h127
              · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
                · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                        · linarith only [h127, h132, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                              · linarith only [h0, h1, h129, h134, h136, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                                · linarith only [h0, h130, h136, h138, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h1, h134, h138, h6, hc23, hlam, hphi, u3elo3]
                            · linarith only [h128, h132, h134, h135, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h127, h134, h6, hc13, hlam, hphi, u3elo3]
                      · linarith only [h127, h131, h5, h6, hc12, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                        · linarith only [h127, h145, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                              · linarith only [h1, h129, h130, h147, h149, h2, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h129, h130, h149, hc23, hlam, hphi, u3elo3]
                            · linarith only [h127, h128, h129, h130, h148, hc23, hlam, hphi, u3elo0]
                          · linarith only [h127, h147, h6, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h129, h144, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h129, h4, h6, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h127, h128, h6, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h157 | h157
                · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                        · linarith only [h1, h161, h6, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
                          · linarith only [h1, h127, h163, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                              · linarith only [h1, h158, h166, h6, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
                                · linarith only [h1, h127, h158, h168, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h170 | h170
                                  · linarith only [h0, h159, h170, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h165, h166, h170, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h157, h158, h161, h165, h6, hc23, hlam, hphi, u3elo3]
                      · linarith only [h127, h158, h160, h5, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                        · linarith only [h1, h157, h176, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h178 | h178
                          · linarith only [h1, h127, h178, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                              · linarith only [h158, h181, h6, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · linarith only [h158, h159, h181, hc23, hlam, hphi, u3elo3]
                            · linarith only [h157, h158, h159, h180, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h158, h175, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h158, h4, h6, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
                        · linarith only [h190, h6, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                          · linarith only [h1, h127, h157, h192, h6, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                            · linarith only [h157, h194, h2, h6, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                              · linarith only [h1, h187, h196, h6, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                                · linarith only [h1, h127, h187, h198, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                                  · linarith only [h1, h157, h187, h188, h200, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h202 | h202
                                    · linarith only [h1, h157, h187, h202, h6, hc23, hlam, hphi, u3elo3]
                                    · rcases h5bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [hlam, p204_0]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h189, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, p204_1, u1elo0]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p204_1, u1elo0]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h127, hlam, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h157, hlam, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h3, hlam, p204_0]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [hlam, p204_0]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p204_1, u1elo4]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h192, hlam, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h194, hlam, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h5, hlam, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h189, hlam, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [hlam, p204_0]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h198, hlam, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h200, hlam, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo4]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h189, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo4]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo4]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [hlam, p204_0]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h202, hlam, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h1, h157, h187, h6, hc23, hc45, hlam, hphi, ht34, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h194, hc14, hc45, hlam, hphi, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h198, hc23, hc45, hlam, hphi, ht34, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [h1, h127, h187, hc23, hc45, hlam, hphi, ht34, p204_1]
                                      · have p204_0 := h204c.1
                                        have p204_1 := h204c.2.1
                                        have p204_2 := h204c.2.2.1
                                        have p204_3 := h204c.2.2.2
                                        linarith only [hlam, p204_0]
                      · linarith only [h127, h187, h189, h5, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h231 | h231
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                        · linarith only [h1, h187, h188, h2, h232, h6, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h234 | h234
                          · linarith only [h1, h127, h234, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
                            · linarith only [h157, h2, h236, hlam]
                            · linarith only [h188, h231, h236, hlam]
                      · linarith only [h0, h187, h231, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h187, h4, h6, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h241 | h241
            · rcases m.htr 0 3 5 (by decide) (by decide) with h242 | h242
              · linarith only [h242, h4, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h244 | h244
                · linarith only [h241, h244, h4, h5, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h247 | h247
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h248 | h248
                      · linarith only [h0, h248, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h251 | h251
                          · linarith only [h242, h251, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h253 | h253
                            · linarith only [h1, h242, h244, h250, h253, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h255 | h255
                              · linarith only [h246, h248, h255, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h241, h242, h255, hc23, hlam, hphi, u3elo4]
                        · linarith only [h241, h242, h250, hc13, hlam, hphi, u3elo4]
                    · linarith only [h2, h241, h242, h246, h247, hc23, hlam, hphi, u3elo4]
                  · linarith only [h246, h4, h5, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h261 | h261
              · linarith only [h241, h261, h4, h5, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
                · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h265 | h265
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h266 | h266
                      · linarith only [h0, h266, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h268 | h268
                        · linarith only [h241, h268, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h270 | h270
                          · linarith only [h0, h1, h261, h264, h270, h5, hc23, hlam, hphi, u3elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                            · linarith only [h265, h266, h272, hlam]
                            · linarith only [h241, h263, h268, h272, hc13, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
                      · linarith only [h0, h275, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                        · linarith only [h241, h277, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                          · linarith only [h0, h1, h261, h264, h279, h5, hc23, hlam, hphi, u3elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
                              · linarith only [h241, h264, h282, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · linarith only [h264, h265, h282, hc23, hlam, hphi, u3elo3]
                            · linarith only [h241, h263, h264, h265, h281, hc23, hlam, hphi, u3elo3]
                  · linarith only [h264, h4, h5, hc12, hc25, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                      · linarith only [h0, h289, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h291 | h291
                        · linarith only [h1, h241, h291, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h293 | h293
                          · linarith only [h1, h261, h293, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                            · linarith only [h2, h263, h295, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
                              · linarith only [h241, h287, h297, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h299 | h299
                                · linarith only [h1, h241, h261, h287, h299, h5, hc02, hlam, hphi, ht23, u3elo3]
                                · linarith only [h299, h4, h5, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
                      · linarith only [h0, h302, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h304 | h304
                        · linarith only [h1, h241, h304, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h306 | h306
                          · linarith only [h1, h261, h306, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                            · linarith only [h2, h263, h308, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                              · linarith only [h241, h287, h310, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · linarith only [h287, h288, h310, hc23, hlam, hphi, u3elo3]
                  · linarith only [h261, h287, h4, h5, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h314 | h314
          · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
            · rcases m.htr 0 3 5 (by decide) (by decide) with h316 | h316
              · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
                · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
                  · linarith only [h314, h318, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h320 | h320
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h322 | h322
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h323 | h323
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h324 | h324
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h325 | h325
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h326 | h326
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h327 | h327
                                  · linarith only [h0, h320, h327, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                  · linarith only [h0, h320, h324, h325, h327, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h326, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h320, h324, h325, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h333 | h333
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h334 | h334
                                  · linarith only [h320, h324, h334, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h336 | h336
                                    · linarith only [h320, h324, h332, h336, hlam]
                                    · rcases h5bigk with h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h0, h314, hc15, hlam, hphi, ht01, ht0b, ht5b, p338_1, u1elo0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h314, h332, h334, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo2]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h314, h336, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo2]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h314, h320, h324, h332, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo2]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h3, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h332, h334, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p338_1, u1elo4]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h3, h314, h336, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo2]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h324, hlam, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h314, hlam, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h321, hlam, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h314, h336, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo2]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h334, hlam, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h316, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h323, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h333, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h336, hlam, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h317, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h315, h317, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p338_1, u3elo2]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h315, h317, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p338_1, u3elo2]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h315, h317, h336, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo2]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                · linarith only [h333, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h315, h317, h322, h324, h332, h4, hlam]
                          · linarith only [h316, h323, hc13, hlam, hphi, u3elo0]
                        · linarith only [h315, h318, h320, h322, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h0, h314, h320, h321, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h369 | h369
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h370 | h370
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h371 | h371
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h372 | h372
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h374 | h374
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h375 | h375
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h376 | h376
                                    · linarith only [h1, h370, h376, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h2, h372, h376, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h1, h320, h369, h370, h372, h374, h375, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h374, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h369, h373, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h315, h317, h320, h369, h372, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h316, h371, h4, hc13, hlam, hphi, u3elo2]
                        · linarith only [h315, h318, h369, h370, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h314, h369, h4, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                  · linarith only [h314, h386, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h389 | h389
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                            · linarith only [h2, h317, h392, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h395 | h395
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h396 | h396
                                  · linarith only [h2, h317, h388, h396, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h398 | h398
                                    · linarith only [h2, h317, h388, h394, h398, hlam]
                                    · rcases h5bigk with h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [hlam, p400_0]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h314, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p400_1, u3elo2]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h314, h394, h396, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p400_1, u3elo2]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h314, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p400_1, u3elo2]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h317, hlam, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h3, hlam, p400_0]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [hlam, p400_0]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h394, h396, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p400_1, u1elo4]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h3, h314, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p400_1, u3elo2]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h392, hlam, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h314, hlam, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h389, hlam, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [hlam, p400_0]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h314, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p400_1, u3elo2]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h396, hlam, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h316, hlam, p400_0]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h391, hlam, p400_0]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h395, hlam, p400_0]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [hlam, p400_0]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h398, hlam, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h2, h317, h388, h394, hc34, hc45, hlam, hphi, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h388, h392, h394, hc34, hc45, hlam, hphi, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h394, h396, hc34, hc45, hlam, hphi, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [h398, hc34, hc45, hlam, hphi, p400_1]
                                      · have p400_0 := h400c.1
                                        have p400_1 := h400c.2.1
                                        have p400_2 := h400c.2.2.1
                                        have p400_3 := h400c.2.2.2
                                        linarith only [hlam, p400_0]
                                · linarith only [h395, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h388, h394, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h316, h386, h388, h391, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h315, h386, h388, h390, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h314, h388, h389, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h432 | h432
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h433 | h433
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h434 | h434
                            · linarith only [h1, h317, h432, h434, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · linarith only [h388, h431, h434, hlam]
                          · linarith only [h316, h388, h4, h432, h433, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h315, h386, h4, h431, h432, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h314, h4, h431, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h314, h316, h4, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h441 | h441
              · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                  · linarith only [h0, h315, h4, h443, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                        · linarith only [h0, h315, h4, h445, h447, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · linarith only [h443, h445, h447, hlam]
                      · linarith only [h314, h315, h4, h445, h446, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h451 | h451
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
                        · linarith only [h315, h441, h452, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h454 | h454
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h455 | h455
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h456 | h456
                              · linarith only [h0, h315, h4, h451, h456, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h0, h4, h451, h456, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h315, h442, h452, h455, hc13, hlam, hphi, u3elo3]
                          · linarith only [h441, h443, h451, h454, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                      · linarith only [h314, h315, h4, h451, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h314, h315, h4, h442, hlam]
              · linarith only [h314, h4, h441, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h464 | h464
            · rcases m.htr 0 3 5 (by decide) (by decide) with h465 | h465
              · rcases m.htr 0 4 5 (by decide) (by decide) with h466 | h466
                · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
                  · linarith only [h0, h4, h467, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                      · linarith only [h0, h314, h470, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
                            · linarith only [h469, h470, h474, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h476 | h476
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h477 | h477
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                                  · linarith only [h469, h470, h474, h478, hlam]
                                  · linarith only [h0, h314, h4, h464, h466, h469, h476, h478, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h4, h464, h466, h473, h477, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                              · linarith only [h4, h464, h466, h470, h474, h476, hc12, hlam, hphi, ht23, u3elo3]
                          · linarith only [h4, h465, h473, hc13, hlam, hphi, u3elo2]
                        · linarith only [h4, h464, h467, h469, h472, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h485 | h485
                      · linarith only [h0, h314, h485, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h488 | h488
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h491 | h491
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h492 | h492
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h493 | h493
                                    · linarith only [h1, h487, h493, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h2, h489, h493, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h1, h487, h489, h492, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h1, h4, h488, h491, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h0, h4, h490, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h464, h466, h469, h489, hc12, hlam, hphi, ht23, u3elo0]
                          · linarith only [h4, h465, h488, hc13, hlam, hphi, u3elo2]
                        · linarith only [h4, h464, h467, h487, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
                  · linarith only [h0, h4, h464, h502, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h505 | h505
                      · linarith only [h0, h314, h505, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h507 | h507
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h508 | h508
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
                            · linarith only [h2, h466, h509, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h511 | h511
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h513 | h513
                                  · linarith only [h0, h314, h466, h504, h513, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h515 | h515
                                    · linarith only [h0, h314, h504, h511, h513, h515, hlam]
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
                                        linarith only [h465, h504, h505, h511, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h314, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h3, hc35, hlam, hphi, ht01, ht0b, ht5b, p517_1, u1elo0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h466, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h3, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h505, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h508, hc35, hlam, hphi, ht01, ht0b, ht5b, p517_1, u1elo2]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h509, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h0, h314, h504, h511, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h504, h505, h511, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h512, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p517_1, u3elo2]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h513, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h465, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h508, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h512, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h515, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h0, h314, h504, h511, hc34, hc45, hlam, hphi, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h504, h505, h511, hc34, hc45, hlam, hphi, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h0, h314, h504, h511, hc34, hc45, hlam, hphi, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h515, hc34, hc45, hlam, hphi, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hlam, p517_0]
                                · linarith only [h0, h4, h504, h511, h512, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · linarith only [h4, h511, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h465, h508, hc13, hlam, hphi, u3elo0]
                        · linarith only [h4, h464, h502, h504, h507, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h547 | h547
                      · linarith only [h0, h314, h547, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h549 | h549
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h551 | h551
                            · linarith only [h2, h466, h551, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h554 | h554
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h555 | h555
                                  · linarith only [h2, h466, h504, h553, h555, hc12, hlam, hphi, ht23, u3elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h557 | h557
                                    · linarith only [h1, h549, h557, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · rcases h5bigk with h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h3, hc15, hlam, hphi, ht01, ht0b, ht5b, p559_1, u1elo0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h314, hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h4, h465, h557, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p559_1, u3elo2]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h466, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h3, hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h547, hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h557, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p559_1, u1elo4]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h551, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h0, h314, hc12, hc25, hlam, hphi, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h547, hc12, hc25, hlam, hphi, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h554, h557, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p559_1, u3elo2]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h555, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h465, hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h550, hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h554, hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h557, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h2, h466, h504, hc12, hc45, hlam, hphi, ht23, ht34, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h504, h551, hc12, hc45, hlam, hphi, ht23, ht34, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h0, h314, hc12, hc45, hlam, hphi, ht23, ht34, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h557, hc34, hc45, hlam, hphi, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                · linarith only [h0, h4, h554, hc12, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h4, h553, hc12, hlam, hphi, ht23, u3elo3]
                          · linarith only [h465, h549, h550, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h4, h464, h502, h549, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h589 | h589
                · linarith only [h464, h465, h589, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h591 | h591
                  · linarith only [h0, h4, h591, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h593 | h593
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h594 | h594
                      · linarith only [h0, h314, h594, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h596 | h596
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h597 | h597
                          · linarith only [h0, h4, h465, h593, h597, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h599 | h599
                            · linarith only [h0, h4, h465, h589, h593, h599, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h601 | h601
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h602 | h602
                                · linarith only [h4, h465, h602, hc02, hlam, hphi, ht23, u3elo2]
                                · linarith only [h0, h4, h593, h601, h602, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · linarith only [h0, h4, h593, h601, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h464, h596, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h607 | h607
                      · linarith only [h2, h314, h464, h465, h593, h607, hc02, hlam, hphi, ht23, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h609 | h609
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h610 | h610
                          · linarith only [h1, h465, h610, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h612 | h612
                            · linarith only [h2, h589, h612, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h614 | h614
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h615 | h615
                                · linarith only [h1, h465, h609, h615, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h4, h615, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h4, h609, h614, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h464, h465, h609, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h620 | h620
              · rcases m.htr 0 4 5 (by decide) (by decide) with h621 | h621
                · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
                  · linarith only [h0, h4, h622, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h624 | h624
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
                      · linarith only [h0, h314, h625, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h627 | h627
                        · linarith only [h0, h314, h464, h620, h624, h627, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · linarith only [h622, h624, h627, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h630 | h630
                      · linarith only [h0, h314, h630, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h632 | h632
                        · linarith only [h314, h464, h620, h632, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h634 | h634
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h635 | h635
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h636 | h636
                              · linarith only [h1, h464, h634, h636, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h0, h4, h636, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h2, h621, h632, h634, h635, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h620, h634, hc13, hlam, hphi, u3elo0]
                · linarith only [h464, h620, h621, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h642 | h642
                · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
                  · linarith only [h0, h4, h643, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h645 | h645
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h646 | h646
                      · linarith only [h0, h314, h646, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h648 | h648
                        · linarith only [h0, h4, h464, h645, h648, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · linarith only [h643, h645, h648, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h651 | h651
                      · linarith only [h0, h314, h651, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h653 | h653
                        · linarith only [h4, h464, h653, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h655 | h655
                          · linarith only [h1, h620, h655, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h657 | h657
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h658 | h658
                              · linarith only [h0, h4, h464, h658, hc12, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h4, h658, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h464, h642, h645, h657, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
                  · linarith only [h0, h4, h662, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h664 | h664
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h665 | h665
                      · linarith only [h0, h314, h665, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                        · linarith only [h1, h464, h667, hlam]
                        · linarith only [h662, h664, h667, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h670 | h670
                      · linarith only [h0, h314, h670, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h672 | h672
                        · linarith only [h4, h464, h672, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h674 | h674
                          · linarith only [h2, h620, h642, h672, h674, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h676 | h676
                            · linarith only [h1, h2, h464, h642, h662, h676, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h678 | h678
                              · linarith only [h1, h464, h662, h678, hc12, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h4, h678, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h681 | h681
        · rcases m.htr 0 2 5 (by decide) (by decide) with h682 | h682
          · linarith only [h0, h3, h682, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h684 | h684
            · rcases m.htr 0 3 5 (by decide) (by decide) with h685 | h685
              · linarith only [h1, h3, h685, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h687 | h687
                · linarith only [h2, h3, h687, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h689 | h689
                  · linarith only [h0, h3, h689, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · linarith only [h0, h3, h681, h689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h692 | h692
              · linarith only [h0, h3, h681, h684, h692, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h694 | h694
                · linarith only [h2, h3, h694, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h696 | h696
                  · linarith only [h0, h3, h696, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · linarith only [h681, h682, h696, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h699 | h699
          · linarith only [h0, h3, h699, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h701 | h701
            · rcases m.htr 0 3 5 (by decide) (by decide) with h702 | h702
              · linarith only [h1, h3, h702, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h704 | h704
                · linarith only [h0, h3, h701, h702, h704, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h706 | h706
                  · linarith only [h0, h681, h702, h706, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h708 | h708
                    · linarith only [h0, h3, h708, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h710 | h710
                      · linarith only [h1, h3, h699, h706, h710, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h712 | h712
                        · linarith only [h1, h3, h712, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h701, h702, h712, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h715 | h715
              · linarith only [h0, h3, h701, h715, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h717 | h717
                · linarith only [h2, h3, h717, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h719 | h719
                  · linarith only [h0, h681, h719, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h721 | h721
                    · linarith only [h1, h3, h719, h721, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h723 | h723
                      · linarith only [h1, h3, h719, h723, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h725 | h725
                        · linarith only [h1, h3, h701, h725, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h727 | h727
                          · linarith only [h2, h3, h715, h725, h727, hlam]
                          · linarith only [h2, h3, h719, h725, h727, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h730 | h730
      · rcases m.htr 0 2 3 (by decide) (by decide) with h731 | h731
        · rcases m.htr 0 2 5 (by decide) (by decide) with h732 | h732
          · rcases m.htr 0 3 4 (by decide) (by decide) with h733 | h733
            · linarith only [h1, h2, h733, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h735 | h735
              · rcases m.htr 0 4 5 (by decide) (by decide) with h736 | h736
                · rcases m.htr 1 2 3 (by decide) (by decide) with h737 | h737
                  · linarith only [h0, h2, h737, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h731, h737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h731, h733, h735, h736, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h741 | h741
                · rcases m.htr 1 2 3 (by decide) (by decide) with h742 | h742
                  · linarith only [h0, h2, h742, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h731, h742, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h732, h741, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h746 | h746
            · linarith only [h1, h2, h746, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h748 | h748
              · linarith only [h731, h732, h746, h748, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h750 | h750
                · rcases m.htr 1 2 3 (by decide) (by decide) with h751 | h751
                  · linarith only [h0, h2, h751, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h731, h732, h751, hc12, hc25, hlam, hphi]
                · linarith only [h2, h730, h750, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h755 | h755
          · rcases m.htr 0 3 4 (by decide) (by decide) with h756 | h756
            · linarith only [h1, h2, h756, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h758 | h758
              · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
                · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
                  · linarith only [h0, h731, h756, h760, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h762 | h762
                    · linarith only [h0, h2, h762, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h764 | h764
                      · linarith only [h1, h2, h760, h764, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · linarith only [h731, h755, h756, h764, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h1, h2, h731, h755, h756, h759, hc13, hlam, hphi, u3elo3]
              · linarith only [h731, h755, h758, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h769 | h769
            · linarith only [h1, h2, h769, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h771 | h771
              · rcases m.htr 0 4 5 (by decide) (by decide) with h772 | h772
                · rcases m.htr 1 2 3 (by decide) (by decide) with h773 | h773
                  · linarith only [h0, h755, h769, h771, h773, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h775 | h775
                    · linarith only [h0, h2, h775, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h777 | h777
                      · linarith only [h1, h2, h755, h773, h777, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h779 | h779
                        · linarith only [h1, h2, h769, h779, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h1, h2, h779, hc13, hlam, hphi, u3elo3]
                · linarith only [h1, h2, h771, h772, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h783 | h783
                · rcases m.htr 1 2 3 (by decide) (by decide) with h784 | h784
                  · linarith only [h0, h731, h784, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h786 | h786
                    · linarith only [h1, h2, h784, h786, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h788 | h788
                      · linarith only [h0, h755, h788, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h790 | h790
                        · linarith only [h1, h2, h769, h790, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h1, h2, h784, h790, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h2, h730, h783, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h794 | h794
        · rcases m.htr 0 2 5 (by decide) (by decide) with h795 | h795
          · linarith only [h0, h730, h795, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h797 | h797
            · linarith only [h1, h2, h797, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h799 | h799
              · linarith only [h0, h730, h794, h799, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h801 | h801
                · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                  · linarith only [h0, h2, h802, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h794, h802, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
                  · linarith only [h0, h2, h805, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h794, h805, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h808 | h808
          · linarith only [h0, h730, h808, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h810 | h810
            · linarith only [h1, h2, h810, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h812 | h812
              · linarith only [h0, h730, h810, h812, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h814 | h814
                · rcases m.htr 1 2 3 (by decide) (by decide) with h815 | h815
                  · linarith only [h0, h2, h815, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h817 | h817
                    · linarith only [h0, h2, h817, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h819 | h819
                      · linarith only [h1, h2, h808, h815, h819, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h821 | h821
                        · linarith only [h1, h2, h810, h821, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h0, h2, h821, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h824 | h824
                  · linarith only [h0, h794, h824, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h826 | h826
                    · linarith only [h1, h2, h824, h826, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h828 | h828
                      · linarith only [h1, h2, h824, h828, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h830 | h830
                        · linarith only [h1, h2, h830, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · linarith only [h1, h2, h824, h830, hc12, hlam, hphi, ht23, u3elo3]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
