import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_14_L_I_L_0_L_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h12, h4, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h15, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h15, h4, hc23, hlam, hphi, u3elo0]
                      · linarith only [h10, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                    · linarith only [h4, h9, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h21, h6, h8, hlam]
                      · linarith only [h21, h5, hc13, hlam, hphi, u3elo0]
                    · linarith only [h20, h4, h6, hc23, hlam, hphi, u3elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                    · linarith only [h26, h6, h7, hlam]
                    · linarith only [h26, h4, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h29, h6, h7, hlam]
                    · linarith only [h29, h4, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                · linarith only [h32, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                              · linarith only [h32, h34, h38, h40, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                              · linarith only [h32, h34, h35, h37, h40, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h39, h5, h6, hc13, hlam, hphi, u3elo0]
                          · linarith only [h34, h37, h38, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                        · linarith only [h32, h34, h37, hlam]
                      · linarith only [h35, h36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                    · linarith only [h35, h4, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                                · linarith only [h4, h54, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                                · linarith only [h48, h50, h54, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi3]
                              · linarith only [h3, h32, h5, h50, h53, hc12, hlam, hphi, ht23, u3elo0]
                            · linarith only [h49, h52, h6, hlam]
                          · linarith only [h4, h51, h6, hc13, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                              · linarith only [h50, h60, h62, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                                · linarith only [h48, h62, h64, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                · rcases h1bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    rcases p66_3 (m.d 0 1) (by simp) with h68 | h68
                                    · rcases p66_3 (m.d 1 2) (by simp) with h69 | h69
                                      · linarith only [h69, hlam, p66_0]
                                      · rcases p66_3 (m.d 1 3) (by simp) with h71 | h71
                                        · linarith only [h1, h71, hlam]
                                        · linarith only [h6, h71, hlam]
                                    · linarith only [h68, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h49, h64, hc01, hlam, hphi, ht0b, ht45, ht5b, p66_1, u4ehi3]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    rcases p66_3 (m.d 0 1) (by simp) with h76 | h76
                                    · rcases p66_3 (m.d 1 2) (by simp) with h77 | h77
                                      · linarith only [h0, h77, hlam]
                                      · rcases p66_3 (m.d 1 3) (by simp) with h79 | h79
                                        · linarith only [h1, h79, hlam]
                                        · linarith only [h48, h79, hlam]
                                    · linarith only [h76, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    rcases p66_3 (m.d 0 1) (by simp) with h83 | h83
                                    · rcases p66_3 (m.d 1 2) (by simp) with h84 | h84
                                      · linarith only [h0, h84, hlam]
                                      · rcases p66_3 (m.d 1 3) (by simp) with h86 | h86
                                        · linarith only [h1, h86, hlam]
                                        · linarith only [h49, h86, hlam]
                                    · linarith only [h83, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h0, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h6, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h32, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h34, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h1, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h1, hc12, hlam, hphi, ht23, p66_1, u3elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h1, h48, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0, u4ehi3]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h1, h34, hc12, hlam, hphi, ht23, p66_1, u3elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h2, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h2, h4, hc12, hlam, hphi, ht23, p66_1, u3elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h48, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h50, hlam, p66_1]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h3, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h3, h5, hc12, hlam, hphi, ht23, p66_1, u3elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h49, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h3, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0, u4ehi1]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                            · linarith only [h1, h49, h61, hc23, hlam, hphi, u3elo0]
                          · linarith only [h4, h6, h60, hc13, hlam, hphi, u3elo0]
                      · linarith only [h48, h49, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                    · linarith only [h4, h48, hc13, hlam, hphi, u3elo0]
            · linarith only [h4, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h115 | h115
            · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
              · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                    · linarith only [h119, h4, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                          · linarith only [h115, h122, h123, h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                              · linarith only [h0, h117, h126, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h122, h126, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h115, h125, h4, hc23, hlam, hphi, u3elo3]
                        · linarith only [h119, h121, h122, hlam]
                      · linarith only [h115, h121, h4, hc13, hlam, hphi, u3elo3]
                  · linarith only [h115, h116, h118, h3, h4, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                    · linarith only [h134, h4, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                          · linarith only [h115, h116, h137, h138, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h116, h117, h138, hc23, hlam, hphi, u3elo3]
                        · linarith only [h115, h116, h117, h137, h3, h4, hc23, hlam, hphi, u3elo3]
                      · linarith only [h115, h136, h4, hc13, hlam, hphi, u3elo3]
                  · linarith only [h115, h116, h133, h3, h4, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h144 | h144
                · linarith only [h1, h116, h144, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h147 | h147
                    · linarith only [h1, h147, h4, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                          · linarith only [h151, h4, hc03, hlam, hphi, u3elo2]
                          · linarith only [h116, h146, h150, h151, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                        · linarith only [h144, h146, h150, hlam]
                      · linarith only [h115, h116, h149, hc12, hlam, hphi, ht23, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                    · linarith only [h156, h4, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                          · linarith only [h115, h159, h160, h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                          · linarith only [h116, h160, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h156, h158, h159, hlam]
                      · linarith only [h115, h158, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
              · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
                · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                    · linarith only [h168, h4, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                      · linarith only [h1, h115, h170, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h172 | h172
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                          · linarith only [h1, h115, h165, h172, h173, h2, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                            · linarith only [h115, h175, hc03, hlam, hphi, u3elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h177 | h177
                              · linarith only [h0, h166, h177, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h172, h177, h2, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                          · linarith only [h1, h115, h165, h180, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
                            · linarith only [h1, h115, h165, h182, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                              · linarith only [h0, h166, h184, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                                · linarith only [h168, h172, h186, hc13, hlam, hphi, u3elo3]
                                · rcases h1bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h166, hc01, hlam, hphi, ht0b, ht45, ht5b, p188_1, u4ehi2]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    rcases p188_3 (m.d 0 1) (by simp) with h191 | h191
                                    · rcases p188_3 (m.d 1 2) (by simp) with h192 | h192
                                      · linarith only [h0, h192, hlam]
                                      · linarith only [h165, h192, hlam]
                                    · linarith only [h191, hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    rcases p188_3 (m.d 0 1) (by simp) with h196 | h196
                                    · rcases p188_3 (m.d 1 2) (by simp) with h197 | h197
                                      · linarith only [h0, h197, hlam]
                                      · linarith only [h166, h197, hlam]
                                    · linarith only [h196, hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    rcases p188_3 (m.d 0 1) (by simp) with h201 | h201
                                    · rcases p188_3 (m.d 1 2) (by simp) with h202 | h202
                                      · linarith only [h0, h202, hlam]
                                      · linarith only [h167, h202, hlam]
                                    · linarith only [h201, hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h0, hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    rcases p188_3 (m.d 0 1) (by simp) with h208 | h208
                                    · rcases p188_3 (m.d 1 2) (by simp) with h209 | h209
                                      · rcases p188_3 (m.d 1 3) (by simp) with h210 | h210
                                        · linarith only [h165, h210, hlam]
                                        · rcases p188_3 (m.d 1 4) (by simp) with h212 | h212
                                          · linarith only [h166, h212, hlam]
                                          · linarith only [h168, h212, hlam]
                                      · linarith only [h165, h209, hlam]
                                    · linarith only [h1, h208, hlam]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h0, h166, hc01, hlam, hphi, ht0b, ht45, ht5b, p188_1, u4ehi2]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h0, h167, h184, hc01, hlam, hphi, ht0b, ht45, ht5b, p188_1, u4ehi2]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h1, hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h165, hlam, p188_1]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h168, hlam, p188_1]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h170, hlam, p188_1]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h2, hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h166, hlam, p188_1]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h186, h2, h4, hc13, hc45, hlam, hphi, ht34, p188_1]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h172, hlam, p188_1]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h3, hlam, p188_0]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h167, hlam, p188_1]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h115, h165, h3, hc23, hlam, hphi, p188_1, u3elo4]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [h115, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p188_1, u3elo4, u4ehi1]
                                  · have p188_0 := h188c.1
                                    have p188_1 := h188c.2.1
                                    have p188_2 := h188c.2.2.1
                                    have p188_3 := h188c.2.2.2
                                    linarith only [hlam, p188_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                    · linarith only [h1, h234, h4, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
                      · linarith only [h1, h115, h167, h236, h3, h4, hc12, hlam, hphi, ht23, u3elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                        · linarith only [h166, h167, h238, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                          · linarith only [h1, h165, h240, h4, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h242 | h242
                            · linarith only [h1, h115, h165, h167, h242, h3, h4, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h166, h167, h242, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                    · linarith only [h1, h246, h4, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h248 | h248
                      · linarith only [h1, h115, h248, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h250 | h250
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                          · linarith only [h251, h4, hc03, hlam, hphi, u3elo2]
                          · linarith only [h165, h166, h251, hc23, hlam, hphi, u3elo3]
                        · linarith only [h166, h245, h250, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h255 | h255
                    · linarith only [h1, h255, h4, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
                      · linarith only [h1, h115, h257, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h260 | h260
                          · linarith only [h165, h166, h260, h4, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h165, h166, h260, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                          · linarith only [h165, h166, h263, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                          · linarith only [h165, h166, h263, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                · linarith only [h1, h165, h266, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h269 | h269
                    · linarith only [h1, h269, h4, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                      · linarith only [h1, h115, h271, hlam]
                      · linarith only [h165, h268, h271, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
                    · linarith only [h1, h274, h4, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
                      · linarith only [h1, h115, h276, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                          · linarith only [h279, h4, hc03, hlam, hphi, u3elo2]
                          · linarith only [h165, h279, hc12, hlam, hphi, ht23, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
                          · linarith only [h1, h165, h282, h4, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h165, h282, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h285 | h285
          · rcases m.htr 0 3 5 (by decide) (by decide) with h286 | h286
            · linarith only [h1, h286, h3, hlam]
            · linarith only [h285, h286, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
            · linarith only [h1, h285, h289, h3, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
              · linarith only [h0, h289, h291, h3, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                · linarith only [h1, h289, h291, h293, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h295 | h295
                  · linarith only [h1, h291, h295, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h297 | h297
                    · linarith only [h1, h285, h289, h297, h3, hc03, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h299 | h299
                      · linarith only [h2, h289, h297, h299, h3, hlam]
                      · linarith only [h2, h291, h297, h299, h3, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h302 | h302
        · rcases m.htr 0 3 4 (by decide) (by decide) with h303 | h303
          · linarith only [h1, h2, h303, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h305 | h305
            · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
              · linarith only [h0, h2, h303, h306, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h308 | h308
                · linarith only [h1, h2, h303, h306, h308, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h310 | h310
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h311 | h311
                    · linarith only [h1, h2, h303, h311, hlam]
                    · linarith only [h1, h2, h306, h311, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h314 | h314
                    · linarith only [h1, h2, h303, h314, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1, h2, h306, h314, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
              · linarith only [h0, h2, h303, h317, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                · linarith only [h1, h2, h303, h317, h319, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h322 | h322
                    · linarith only [h1, h2, h303, h322, hlam]
                    · linarith only [h1, h2, h317, h322, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h325 | h325
                    · linarith only [h1, h2, h303, h325, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h325, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h328 | h328
          · linarith only [h1, h2, h328, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h330 | h330
            · linarith only [h1, h302, h328, h330, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
              · linarith only [h0, h2, h328, h332, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
                · linarith only [h1, h2, h328, h332, h334, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h336 | h336
                  · linarith only [h1, h302, h332, h336, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h338 | h338
                    · linarith only [h1, h2, h328, h338, hlam]
                    · linarith only [h1, h2, h332, h338, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h342 | h342
    · rcases m.htr 0 1 4 (by decide) (by decide) with h343 | h343
      · rcases m.htr 0 1 5 (by decide) (by decide) with h344 | h344
        · rcases m.htr 0 3 4 (by decide) (by decide) with h345 | h345
          · rcases m.htr 0 3 5 (by decide) (by decide) with h346 | h346
            · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
              · rcases m.htr 1 2 4 (by decide) (by decide) with h348 | h348
                · rcases m.htr 1 2 5 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h350 | h350
                    · linarith only [h0, h342, h350, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h345, h350, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h342, h345, h349, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h0, h342, h345, h348, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h342, h345, h347, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h345, h346, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h357 | h357
            · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
              · rcases m.htr 1 2 4 (by decide) (by decide) with h359 | h359
                · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h361 | h361
                    · linarith only [h345, h361, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h363 | h363
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                        · linarith only [h0, h343, h364, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h361, h363, h364, hlam]
                      · linarith only [h345, h357, h363, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h343, h359, h360, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · linarith only [h0, h343, h359, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h343, h358, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
              · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
                · rcases m.htr 1 2 5 (by decide) (by decide) with h373 | h373
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h374 | h374
                    · linarith only [h0, h342, h345, h374, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h376 | h376
                      · linarith only [h342, h357, h376, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h378 | h378
                        · linarith only [h0, h343, h378, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                          · linarith only [h342, h345, h371, h380, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h382 | h382
                            · linarith only [h342, h357, h371, h382, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h384 | h384
                              · linarith only [h372, h378, h384, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h386 | h386
                                · linarith only [h374, h378, h386, hc13, hlam, hphi, u3elo3]
                                · rcases h1bigk with h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h0, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    rcases p388_3 (m.d 0 1) (by simp) with h391 | h391
                                    · rcases p388_3 (m.d 1 2) (by simp) with h392 | h392
                                      · rcases p388_3 (m.d 1 3) (by simp) with h393 | h393
                                        · linarith only [h393, hlam, p388_0]
                                        · rcases p388_3 (m.d 1 4) (by simp) with h395 | h395
                                          · linarith only [h343, h395, hlam]
                                          · linarith only [h374, h395, hlam]
                                      · linarith only [h371, h392, hlam]
                                    · linarith only [h391, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h0, h372, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p388_1, u4ehi2]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h0, h373, h384, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p388_1, u4ehi2]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h343, h372, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p388_1, u4ehi2]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    rcases p388_3 (m.d 0 1) (by simp) with h404 | h404
                                    · linarith only [h0, h404, hlam]
                                    · linarith only [h342, h404, hlam]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    rcases p388_3 (m.d 0 1) (by simp) with h407 | h407
                                    · linarith only [h0, h407, hlam]
                                    · linarith only [h343, h407, hlam]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    rcases p388_3 (m.d 0 1) (by simp) with h410 | h410
                                    · linarith only [h0, h410, hlam]
                                    · linarith only [h344, h410, hlam]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h342, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h371, hlam, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h374, hlam, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h376, hlam, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h343, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h372, hlam, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h0, h343, h371, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h378, hlam, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h344, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h373, hlam, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h0, h344, h371, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h0, h344, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p388_1, u4ehi1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                  · linarith only [h0, h343, h372, h373, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · linarith only [h0, h343, h372, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h343, h371, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h431 | h431
          · rcases m.htr 0 3 5 (by decide) (by decide) with h432 | h432
            · linarith only [h342, h344, h432, hlam]
            · linarith only [h431, h432, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h435 | h435
            · linarith only [h343, h344, h431, h435, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
              · rcases m.htr 1 2 4 (by decide) (by decide) with h438 | h438
                · rcases m.htr 1 2 5 (by decide) (by decide) with h439 | h439
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h440 | h440
                    · linarith only [h342, h344, h431, h439, h440, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h442 | h442
                      · linarith only [h342, h343, h344, h431, h435, h438, h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                      · linarith only [h343, h344, h438, h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi2]
                  · linarith only [h0, h343, h438, h439, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · linarith only [h0, h343, h438, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h343, h437, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h448 | h448
        · rcases m.htr 0 3 4 (by decide) (by decide) with h449 | h449
          · linarith only [h342, h343, h449, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h451 | h451
            · rcases m.htr 1 2 3 (by decide) (by decide) with h452 | h452
              · rcases m.htr 1 2 4 (by decide) (by decide) with h453 | h453
                · rcases m.htr 1 2 5 (by decide) (by decide) with h454 | h454
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h455 | h455
                    · linarith only [h342, h343, h449, h453, h455, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h342, h343, h455, hc13, hlam, hphi, u3elo3]
                  · linarith only [h343, h448, h453, h454, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                    · linarith only [h0, h342, h449, h453, h460, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · linarith only [h342, h343, h460, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h448, h459, hlam]
              · linarith only [h0, h452, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h465 | h465
              · rcases m.htr 1 2 4 (by decide) (by decide) with h466 | h466
                · rcases m.htr 1 2 5 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h468 | h468
                    · linarith only [h342, h343, h466, h468, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h342, h343, h468, hc13, hlam, hphi, u3elo3]
                  · linarith only [h343, h448, h466, h467, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h473 | h473
                    · linarith only [h0, h342, h449, h466, h473, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · linarith only [h0, h342, h465, h466, h473, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h448, h472, hlam]
              · linarith only [h0, h465, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h478 | h478
          · linarith only [h342, h343, h478, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h480 | h480
            · linarith only [h342, h448, h478, h480, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h482 | h482
              · rcases m.htr 1 2 4 (by decide) (by decide) with h483 | h483
                · rcases m.htr 1 2 5 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h485 | h485
                    · linarith only [h342, h448, h478, h485, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h342, h343, h482, h485, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                    · linarith only [h342, h343, h478, h488, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h342, h343, h488, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h491 | h491
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h492 | h492
                    · linarith only [h342, h448, h483, h491, h492, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h342, h448, h482, h483, h491, h492, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h495 | h495
                    · linarith only [h0, h342, h495, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h342, h483, h495, hc13, hlam, hphi, u3elo3]
              · linarith only [h0, h342, h482, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h499 | h499
      · linarith only [h342, h499, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h501 | h501
        · rcases m.htr 0 3 4 (by decide) (by decide) with h502 | h502
          · rcases m.htr 0 3 5 (by decide) (by decide) with h503 | h503
            · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
              · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
                · rcases m.htr 1 2 5 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h507 | h507
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h508 | h508
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
                        · linarith only [h499, h501, h507, h509, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
                        · linarith only [h499, h501, h509, hlam]
                      · linarith only [h342, h502, h508, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                    · linarith only [h342, h502, h507, hlam]
                  · linarith only [h342, h499, h501, h502, h504, h506, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                    · linarith only [h504, h505, h516, hlam]
                    · linarith only [h342, h502, h516, hlam]
                  · linarith only [h342, h501, h504, h515, hlam]
              · linarith only [h0, h504, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h502, h503, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h522 | h522
            · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
              · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
                · rcases m.htr 1 2 5 (by decide) (by decide) with h525 | h525
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
                    · linarith only [h502, h522, h526, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h342, h501, h525, h526, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h342, h501, h524, h525, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h530 | h530
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h531 | h531
                    · linarith only [h342, h502, h523, h524, h531, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h342, h501, h530, h531, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h342, h501, h523, h530, hc23, hlam, hphi, u3elo0]
              · linarith only [h0, h523, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h342, h501, h522, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h537 | h537
          · rcases m.htr 0 3 5 (by decide) (by decide) with h538 | h538
            · rcases m.htr 1 2 3 (by decide) (by decide) with h539 | h539
              · rcases m.htr 1 2 4 (by decide) (by decide) with h540 | h540
                · rcases m.htr 1 2 5 (by decide) (by decide) with h541 | h541
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h543 | h543
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h544 | h544
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h546 | h546
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h547 | h547
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h548 | h548
                                · linarith only [h537, h548, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                                · linarith only [h539, h545, h547, h548, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h542, h544, h547, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi2]
                            · linarith only [h342, h538, h545, h546, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi3]
                          · linarith only [h342, h537, h545, hc23, hlam, hphi, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h554 | h554
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h556 | h556
                              · linarith only [h499, h544, h556, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h558 | h558
                                · linarith only [h342, h499, h537, h544, h558, hc01, hlam, hphi, ht12, ht23, u3elo1]
                                · rcases h1bigk with h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h0, hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h342, hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h499, hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h501, hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    rcases p560_3 (m.d 0 1) (by simp) with h566 | h566
                                    · linarith only [h566, hlam, p560_0]
                                    · rcases p560_3 (m.d 1 2) (by simp) with h568 | h568
                                      · rcases p560_3 (m.d 1 3) (by simp) with h569 | h569
                                        · linarith only [h539, h569, hlam]
                                        · linarith only [h342, h569, hlam]
                                      · linarith only [h568, hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h342, h538, h558, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p560_1, u4ehi3]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h499, hc01, hc12, hlam, hphi, p560_1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h499, h544, hc01, hc12, hlam, hphi, p560_1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p560_1, u3elo1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h539, hlam, p560_1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h499, hc01, hlam, hphi, ht12, ht23, p560_1, u3elo1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h499, h544, hc01, hlam, hphi, ht12, ht23, p560_1, u3elo1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h544, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p560_1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h540, hlam, p560_1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h542, hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h544, hlam, p560_1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h543, hc01, hlam, hphi, ht12, ht23, p560_1, u3elo1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h541, hlam, p560_1]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h543, hlam, p560_0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [h499, h543, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p560_1, u3elo1, u4ehi0]
                                  · have p560_0 := h560c.1
                                    have p560_1 := h560c.2.1
                                    have p560_2 := h560c.2.2.1
                                    have p560_3 := h560c.2.2.2
                                    linarith only [hlam, p560_0]
                            · linarith only [h342, h538, h555, hc23, hlam, hphi, u3elo1]
                          · linarith only [h342, h537, h554, hc23, hlam, hphi, u3elo1]
                      · linarith only [h342, h538, h543, hlam]
                    · linarith only [h342, h537, h542, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h596 | h596
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h597 | h597
                      · linarith only [h539, h541, h597, hlam]
                      · linarith only [h342, h538, h597, hlam]
                    · linarith only [h342, h537, h596, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h601 | h601
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h602 | h602
                    · linarith only [h539, h540, h602, hlam]
                    · linarith only [h342, h537, h602, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h605 | h605
                    · linarith only [h539, h540, h605, hlam]
                    · linarith only [h342, h537, h605, hlam]
              · linarith only [h0, h539, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h537, h538, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h610 | h610
            · rcases m.htr 1 2 3 (by decide) (by decide) with h611 | h611
              · rcases m.htr 1 2 4 (by decide) (by decide) with h612 | h612
                · rcases m.htr 1 2 5 (by decide) (by decide) with h613 | h613
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h614 | h614
                    · linarith only [h537, h614, hc03, hlam, hphi, u3elo1]
                    · linarith only [h342, h614, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h617 | h617
                    · linarith only [h537, h610, h617, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h342, h617, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h621 | h621
                    · linarith only [h537, h610, h621, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h342, h621, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h624 | h624
                    · linarith only [h537, h610, h624, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h342, h624, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h611, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
              · rcases m.htr 1 2 4 (by decide) (by decide) with h629 | h629
                · rcases m.htr 1 2 5 (by decide) (by decide) with h630 | h630
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h631 | h631
                    · linarith only [h537, h631, hc03, hlam, hphi, u3elo1]
                    · linarith only [h342, h631, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h634 | h634
                    · linarith only [h342, h537, h634, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h342, h634, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h638 | h638
                    · linarith only [h342, h537, h638, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h342, h638, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h641 | h641
                    · linarith only [h342, h537, h641, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h342, h641, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h628, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_11_13_25_L_I_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
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
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h16, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                                  · linarith only [h15, h16, hc34, hlam, hphi, ht45, u5elo3]
                                · linarith only [h15, h7, hc23, hlam, hphi, u3elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                                  · linarith only [h0, h21, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                                  · linarith only [h1, h13, h21, hc23, hlam, hphi, u3elo0]
                                · linarith only [h20, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h12, h13, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h12, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h11, h6, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
                      · linarith only [h10, h5, h7, h9, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                        · linarith only [h30, h4, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi7]
                        · linarith only [h29, h30, hc24, hlam, hphi, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                        · linarith only [h29, h33, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi7]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                                      · linarith only [h41, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi9]
                                      · rcases h1bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          rcases p43_3 (m.d 0 1) (by simp) with h45 | h45
                                          · rcases p43_3 (m.d 1 2) (by simp) with h46 | h46
                                            · linarith only [h46, hlam, p43_0]
                                            · rcases p43_3 (m.d 1 3) (by simp) with h48 | h48
                                              · linarith only [h1, h48, hlam]
                                              · linarith only [h48, h9, hlam]
                                          · linarith only [h45, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h36, hc01, hlam, hphi, ht0b, ht5b, p43_1, u5ehi8]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h37, h41, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p43_1]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          rcases p43_3 (m.d 0 1) (by simp) with h54 | h54
                                          · rcases p43_3 (m.d 1 2) (by simp) with h55 | h55
                                            · linarith only [h0, h55, hlam]
                                            · rcases p43_3 (m.d 1 3) (by simp) with h57 | h57
                                              · linarith only [h1, h57, hlam]
                                              · linarith only [h36, h57, hlam]
                                          · linarith only [h54, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h0, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h9, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h29, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h33, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h1, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [hc12, hlam, hphi, ht23, p43_1, u3elo1]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h37, h4, h41, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h37, h4, h41, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h2, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h2, h7, hc12, hlam, hphi, ht23, p43_1, u3elo0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h35, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h29, h37, h41, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h3, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p43_1, u5elo1]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h36, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [h37, hlam, p43_0]
                                        · have p43_0 := h43c.1
                                          have p43_1 := h43c.2.1
                                          have p43_2 := h43c.2.2.1
                                          have p43_3 := h43c.2.2.2
                                          linarith only [hlam, p43_0]
                                    · linarith only [h29, h37, h40, hlam]
                                  · linarith only [h29, h37, h39, h5, h7, h9, hc12, hlam, hphi, ht23, u3elo0, u5ehi9, u5elo3]
                                · linarith only [h35, h37, h38, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi9]
                              · linarith only [h29, h37, h7, h8, hc12, hlam, hphi, ht23, u3elo0]
                            · linarith only [h35, h36, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h35, h7, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                              · linarith only [h2, h8, h92, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                                  · linarith only [h0, h87, h95, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                                  · linarith only [h91, h95, hc23, hlam, hphi, u3elo1]
                                · linarith only [h7, h94, hc23, hlam, hphi, u3elo0]
                            · linarith only [h90, h91, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h7, h90, hc13, hlam, hphi, u3elo0]
                        · linarith only [h6, h8, h87, h89, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h5, h8, h87, h88, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                        · linarith only [h104, h4, h87, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi7]
                        · linarith only [h103, h104, h6, h8, hc24, hlam, hphi, ht45, u5elo4]
                      · linarith only [h103, h5, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                          · linarith only [h1, h112, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                            · linarith only [h1, h114, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                                · linarith only [h109, h114, h117, h7, hc03, hlam, hphi, ht34, ht45, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                                  · linarith only [h109, h114, h119, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                                    · linarith only [h0, h110, h121, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                    · linarith only [h116, h117, h121, h2, h7, hc23, hlam, hphi, u3elo3]
                              · linarith only [h108, h112, h116, h7, hc13, hlam, hphi, u3elo3]
                        · linarith only [h109, h111, h6, hc23, hlam, hphi, ht34, ht45, u5elo0]
                      · linarith only [h109, h110, h5, h7, hc23, hlam, hphi, u3elo3]
                    · linarith only [h109, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h128 | h128
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                          · linarith only [h1, h108, h131, h7, hc34, hlam, hphi, ht45, u5elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                            · linarith only [h1, h108, h133, h7, hlam, hphi, u5ehi8, u5elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                              · linarith only [h108, h135, h2, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                                · linarith only [h1, h128, h137, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                                  · linarith only [h1, h128, h133, h139, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi6]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                                    · linarith only [h108, h129, h141, h2, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                                      · linarith only [h108, h143, h7, hc03, hlam, hphi, u3elo3]
                                      · linarith only [h1, h128, h143, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h128, h130, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h128, h129, h5, h7, hc23, hlam, hphi, u3elo3]
                    · linarith only [h128, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h150 | h150
              · rcases m.htr 0 3 4 (by decide) (by decide) with h151 | h151
                · linarith only [h151, h4, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h155 | h155
                      · linarith only [h150, h155, h5, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h157 | h157
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                          · linarith only [h151, h158, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                            · linarith only [h1, h151, h160, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h163 | h163
                                · linarith only [h151, h163, hc03, hlam, hphi, u3elo2]
                                · linarith only [h0, h157, h163, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi7]
                              · linarith only [h155, h157, h162, hlam, hphi, u5ehi7, u5elo4]
                        · linarith only [h150, h157, h5, hc12, hc24, hlam, hphi]
                    · linarith only [h151, h154, h4, h5, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h150, h153, h5, hlam, hphi, u5ehi7, u5elo4]
              · linarith only [h150, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h171 | h171
            · rcases m.htr 0 2 5 (by decide) (by decide) with h172 | h172
              · linarith only [h172, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
              · linarith only [h171, h172, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h175 | h175
              · linarith only [h175, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h177 | h177
                · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                    · linarith only [h0, h177, h178, h179, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                      · linarith only [h171, h178, h179, h181, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi9]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h0, h175, h183, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h187 | h187
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h189 | h189
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h190 | h190
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h191 | h191
                                      · linarith only [h177, h191, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi9]
                                      · rcases h1bigk with h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          rcases p193_3 (m.d 0 1) (by simp) with h195 | h195
                                          · rcases p193_3 (m.d 1 2) (by simp) with h196 | h196
                                            · linarith only [h196, hlam, p193_0]
                                            · rcases p193_3 (m.d 1 3) (by simp) with h198 | h198
                                              · linarith only [h1, h198, hlam]
                                              · linarith only [h179, h198, hlam]
                                          · linarith only [h195, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h185, h187, h191, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p193_1]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h187, h191, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p193_1]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          rcases p193_3 (m.d 0 1) (by simp) with h204 | h204
                                          · rcases p193_3 (m.d 1 2) (by simp) with h205 | h205
                                            · linarith only [h0, h205, hlam]
                                            · rcases p193_3 (m.d 1 3) (by simp) with h207 | h207
                                              · linarith only [h1, h207, hlam]
                                              · linarith only [h186, h207, hlam]
                                          · linarith only [h204, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h0, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h179, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h181, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h183, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h1, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [hc12, hlam, hphi, ht23, p193_1, u3elo1]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h1, h187, h191, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p193_1, u3elo2]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h1, h187, h191, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p193_1, u3elo2]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h2, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h177, h2, h4, hc12, hlam, hphi, ht23, p193_1, u3elo2]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h185, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h177, h187, h191, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p193_1, u3elo2]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h3, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p193_1, u5elo1]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h186, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [h187, hlam, p193_0]
                                        · have p193_0 := h193c.1
                                          have p193_1 := h193c.2.1
                                          have p193_2 := h193c.2.2.1
                                          have p193_3 := h193c.2.2.2
                                          linarith only [hlam, p193_0]
                                    · linarith only [h171, h187, h190, h2, hlam]
                                  · linarith only [h177, h187, h189, h2, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi9]
                                · linarith only [h177, h187, h188, h2, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi9]
                              · linarith only [h177, h178, h181, h187, h4, hc12, hlam, hphi, ht23, u3elo2]
                            · linarith only [h185, h186, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h177, h185, h4, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                    · linarith only [h0, h171, h178, h237, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
                      · linarith only [h171, h237, h239, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
                        · linarith only [h0, h175, h241, h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h244 | h244
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                              · linarith only [h178, h2, h245, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h249 | h249
                                    · linarith only [h171, h178, h247, h249, hc02, hlam, hphi, ht23, u3elo2]
                                    · linarith only [h0, h171, h249, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                  · linarith only [h1, h244, h248, h4, hlam]
                                · linarith only [h1, h244, h247, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                            · linarith only [h243, h244, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h177, h243, h4, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h257 | h257
                    · linarith only [h0, h257, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h259 | h259
                      · linarith only [h171, h256, h257, h259, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi9]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h261 | h261
                        · linarith only [h0, h175, h261, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h263 | h263
                          · linarith only [h1, h177, h263, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
                            · linarith only [h1, h177, h265, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h267 | h267
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h268 | h268
                                · linarith only [h177, h268, hc03, hlam, hphi, u3elo2]
                                · linarith only [h268, h4, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h177, h256, h259, h267, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h272 | h272
                    · linarith only [h0, h272, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h274 | h274
                      · linarith only [h0, h171, h274, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h276 | h276
                        · linarith only [h0, h276, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                          · linarith only [h1, h177, h256, h278, hc34, hlam, hphi, ht45, u5elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h280 | h280
                            · linarith only [h1, h177, h256, h280, hlam, hphi, u5ehi8, u5elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h282 | h282
                              · linarith only [h2, h256, h282, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h284 | h284
                                · linarith only [h0, h177, h284, h4, hc12, hlam, hphi, ht23, u3elo2]
                                · linarith only [h0, h284, h4, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h288 | h288
        · rcases m.htr 0 2 3 (by decide) (by decide) with h289 | h289
          · rcases m.htr 0 2 4 (by decide) (by decide) with h290 | h290
            · linarith only [h0, h2, h290, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h292 | h292
              · rcases m.htr 0 3 4 (by decide) (by decide) with h293 | h293
                · linarith only [h1, h2, h293, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                    · linarith only [h0, h2, h293, h296, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h2, h289, h293, h296, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h0, h2, h292, h295, hlam, hphi, u5ehi7, u5elo4]
              · linarith only [h289, h292, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h301 | h301
            · linarith only [h0, h2, h301, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h303 | h303
              · linarith only [h289, h303, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h305 | h305
                · linarith only [h1, h2, h305, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h307 | h307
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h308 | h308
                    · linarith only [h0, h303, h308, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h310 | h310
                      · linarith only [h0, h2, h288, h301, h303, h310, hlam, hphi, u5ehi6, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h312 | h312
                        · linarith only [h0, h303, h312, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h314 | h314
                          · linarith only [h1, h2, h305, h314, hlam]
                          · linarith only [h2, h288, h314, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi6]
                  · linarith only [h2, h288, h307, hlam, hphi, u5ehi6, u5elo4]
        · linarith only [h1, h288, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h320 | h320
    · rcases m.htr 0 1 4 (by decide) (by decide) with h321 | h321
      · rcases m.htr 0 1 5 (by decide) (by decide) with h322 | h322
        · rcases m.htr 0 2 3 (by decide) (by decide) with h323 | h323
          · rcases m.htr 0 2 4 (by decide) (by decide) with h324 | h324
            · rcases m.htr 0 2 5 (by decide) (by decide) with h325 | h325
              · rcases m.htr 0 3 4 (by decide) (by decide) with h326 | h326
                · rcases m.htr 0 4 5 (by decide) (by decide) with h327 | h327
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h328 | h328
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h329 | h329
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h331 | h331
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
                            · linarith only [h0, h320, h332, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                            · linarith only [h331, h332, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h326, h331, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h330, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h320, h326, h327, h329, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h0, h320, h326, h327, h328, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h340 | h340
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h341 | h341
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h342 | h342
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h343 | h343
                            · linarith only [h0, h320, h343, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                            · linarith only [h342, h343, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h326, h339, h342, hc23, hlam, hphi, u3elo0]
                        · linarith only [h0, h341, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h322, h340, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                    · linarith only [h0, h322, h339, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h350 | h350
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h351 | h351
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h352 | h352
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h354 | h354
                          · linarith only [h0, h320, h326, h354, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
                            · linarith only [h320, h326, h356, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h358 | h358
                              · linarith only [h0, h321, h358, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                              · linarith only [h326, h350, h351, h354, h358, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h322, h353, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                      · linarith only [h0, h321, h350, h352, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h0, h321, h350, h351, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h364 | h364
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h366 | h366
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h367 | h367
                          · linarith only [h320, h326, h367, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h369 | h369
                            · linarith only [h320, h326, h350, h369, hlam, hphi, u5ehi8, u5elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h371 | h371
                              · linarith only [h0, h321, h326, h350, h371, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                                · linarith only [h320, h326, h364, h373, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h375 | h375
                                  · linarith only [h320, h326, h364, h366, h369, h375, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi7]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h377 | h377
                                    · linarith only [h321, h350, h365, h377, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
                                      · linarith only [h326, h350, h379, hc03, hlam, hphi, u3elo3]
                                      · linarith only [h320, h326, h364, h379, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h366, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h322, h365, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                    · linarith only [h0, h322, h364, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h322, h325, hlam, hphi, u5ehi6, u5elo2]
            · linarith only [h0, h321, h324, hlam]
          · linarith only [h0, h322, h323, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi6]
        · linarith only [h321, h322, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h389 | h389
        · rcases m.htr 0 2 3 (by decide) (by decide) with h390 | h390
          · rcases m.htr 0 2 4 (by decide) (by decide) with h391 | h391
            · rcases m.htr 0 2 5 (by decide) (by decide) with h392 | h392
              · rcases m.htr 0 3 4 (by decide) (by decide) with h393 | h393
                · linarith only [h320, h321, h393, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h395 | h395
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
                          · linarith only [h393, h399, hc03, hlam, hphi, u3elo1]
                          · linarith only [h321, h389, h398, h399, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi7]
                        · linarith only [h321, h389, h397, h398, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                      · linarith only [h0, h389, h391, h393, h397, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi6]
                    · linarith only [h0, h389, h396, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                  · linarith only [h321, h389, h395, hlam, hphi, u5ehi6, u5elo4]
              · linarith only [h391, h392, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h407 | h407
              · rcases m.htr 0 3 4 (by decide) (by decide) with h408 | h408
                · linarith only [h0, h320, h391, h408, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h410 | h410
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h411 | h411
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
                      · linarith only [h0, h389, h391, h412, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                      · linarith only [h0, h389, h412, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                    · linarith only [h0, h389, h411, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                  · linarith only [h0, h389, h391, h410, hlam, hphi, u5ehi6, u5elo4]
              · linarith only [h0, h389, h407, hlam, hphi, u5ehi6, u5elo2]
          · linarith only [h0, h389, h390, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi6]
        · linarith only [h320, h389, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h420 | h420
      · rcases m.htr 0 1 5 (by decide) (by decide) with h421 | h421
        · linarith only [h320, h421, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi6]
        · linarith only [h420, h421, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h424 | h424
        · linarith only [h320, h424, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi6]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h426 | h426
          · rcases m.htr 0 2 4 (by decide) (by decide) with h427 | h427
            · rcases m.htr 0 2 5 (by decide) (by decide) with h428 | h428
              · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
                · rcases m.htr 0 4 5 (by decide) (by decide) with h430 | h430
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h431 | h431
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h432 | h432
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h433 | h433
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h434 | h434
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h435 | h435
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h436 | h436
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h437 | h437
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h440 | h440
                                      · linarith only [h320, h429, h440, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi9]
                                      · rcases h1bigk with h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h0, hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h320, hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h420, hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h424, hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          rcases p442_3 (m.d 0 1) (by simp) with h448 | h448
                                          · linarith only [h448, hlam, p442_0]
                                          · rcases p442_3 (m.d 1 2) (by simp) with h450 | h450
                                            · rcases p442_3 (m.d 1 3) (by simp) with h451 | h451
                                              · linarith only [h431, h451, hlam]
                                              · linarith only [h320, h451, hlam]
                                            · linarith only [h450, hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h320, hc01, hc12, hlam, hphi, p442_1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h420, h427, h439, h440, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p442_1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h424, hc01, hc12, hlam, hphi, p442_1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, p442_1, u3elo1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h431, hlam, p442_1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h420, h427, h439, h440, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p442_1, u3elo1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h424, hc01, hlam, hphi, ht12, ht23, p442_1, u3elo1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h434, hc01, hlam, hphi, ht12, ht23, p442_1, u3elo1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h432, hlam, p442_1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h434, hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h424, h434, hc01, hlam, hphi, ht12, ht23, p442_1, u3elo1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p442_1, u5elo1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h433, hlam, p442_1]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h435, hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [h436, hlam, p442_0]
                                        · have p442_0 := h442c.1
                                          have p442_1 := h442c.2.1
                                          have p442_2 := h442c.2.2.1
                                          have p442_3 := h442c.2.2.2
                                          linarith only [hlam, p442_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h474 | h474
                                      · linarith only [h437, h439, h474, hlam]
                                      · rcases h1bigk with h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h0, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h320, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h420, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h424, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          rcases p476_3 (m.d 0 1) (by simp) with h482 | h482
                                          · linarith only [h482, hlam, p476_0]
                                          · rcases p476_3 (m.d 1 2) (by simp) with h484 | h484
                                            · rcases p476_3 (m.d 1 3) (by simp) with h485 | h485
                                              · linarith only [h431, h485, hlam]
                                              · linarith only [h320, h485, hlam]
                                            · linarith only [h484, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h420, h430, h434, h437, h439, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h420, h430, h437, h439, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h424, hc01, hc12, hlam, hphi, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, p476_1, u3elo1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h431, hlam, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h420, h430, h437, h439, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p476_1, u3elo1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h424, hc01, hlam, hphi, ht12, ht23, p476_1, u3elo1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h434, hc01, hlam, hphi, ht12, ht23, p476_1, u3elo1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h432, hlam, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h434, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h424, h434, hc01, hlam, hphi, ht12, ht23, p476_1, u3elo1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p476_1, u5elo1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h433, hlam, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h435, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h436, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                  · linarith only [h435, h438, hc23, hlam, hphi, u3elo1]
                                · linarith only [h429, h437, hc23, hlam, hphi, u3elo0]
                              · linarith only [h420, h430, h436, hlam]
                            · linarith only [h420, h430, h434, h435, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi9]
                          · linarith only [h320, h429, h430, h434, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi9]
                        · linarith only [h0, h433, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h427, h432, hlam]
                    · linarith only [h0, h426, h429, h430, h431, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi9]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h516 | h516
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h517 | h517
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h518 | h518
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h519 | h519
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h520 | h520
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                              · linarith only [h420, h430, h519, h521, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · linarith only [h420, h521, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h320, h520, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h320, h519, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h428, h518, hlam]
                      · linarith only [h0, h427, h428, h430, h517, hlam, hphi, u5ehi7, u5elo4]
                    · linarith only [h0, h426, h428, h516, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi7]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h529 | h529
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h530 | h530
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h531 | h531
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h532 | h532
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h533 | h533
                          · linarith only [h320, h429, h533, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h320, h533, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h427, h529, h532, hlam, hphi, u5ehi9, u5elo2]
                      · linarith only [h0, h427, h531, hlam]
                    · linarith only [h0, h426, h427, h529, h530, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi9]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h539 | h539
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h540 | h540
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h541 | h541
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
                          · linarith only [h320, h429, h542, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h320, h542, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h428, h541, hlam]
                      · linarith only [h0, h427, h529, h540, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h320, h428, h429, h529, h539, hc01, hlam, hphi, ht12, ht23, u3elo2, u5ehi7, u5elo4]
              · linarith only [h426, h428, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h549 | h549
              · rcases m.htr 0 3 4 (by decide) (by decide) with h550 | h550
                · linarith only [h426, h427, h550, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h552 | h552
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h553 | h553
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h554 | h554
                      · linarith only [h427, h549, h554, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h556 | h556
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h557 | h557
                          · linarith only [h550, h557, hc03, hlam, hphi, u3elo1]
                          · linarith only [h320, h557, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h556, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h426, h549, h553, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi7]
                  · linarith only [h427, h549, h552, hlam, hphi, u5ehi7, u5elo4]
              · linarith only [h426, h549, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h564 | h564
            · rcases m.htr 0 2 5 (by decide) (by decide) with h565 | h565
              · linarith only [h426, h565, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
              · linarith only [h564, h565, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h568 | h568
              · linarith only [h426, h568, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi7]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h570 | h570
                · rcases m.htr 0 4 5 (by decide) (by decide) with h571 | h571
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h572 | h572
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h573 | h573
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h574 | h574
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h575 | h575
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h577 | h577
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h579 | h579
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h580 | h580
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h581 | h581
                                      · linarith only [h426, h570, h572, h581, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi9]
                                      · rcases h1bigk with h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h0, hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h320, hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h420, hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h424, hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          rcases p583_3 (m.d 0 1) (by simp) with h589 | h589
                                          · linarith only [h589, hlam, p583_0]
                                          · rcases p583_3 (m.d 1 2) (by simp) with h591 | h591
                                            · rcases p583_3 (m.d 1 3) (by simp) with h592 | h592
                                              · linarith only [h572, h592, hlam]
                                              · linarith only [h320, h592, hlam]
                                            · linarith only [h591, hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h320, hc01, hc12, hlam, hphi, p583_1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h0, h420, h568, h571, h574, h581, hc01, hc12, hc34, hlam, hphi, ht45, p583_1, u5elo1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h0, h568, h574, hc01, hc12, hlam, hphi, p583_1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, p583_1, u3elo1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h572, hlam, p583_1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h0, h564, h568, h571, h573, h574, h581, hc01, hc34, hlam, hphi, ht12, ht23, ht45, p583_1, u3elo1, u5elo1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h0, h568, h574, hc01, hlam, hphi, ht12, ht23, p583_1, u3elo1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h575, hc01, hlam, hphi, ht12, ht23, p583_1, u3elo1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h573, hlam, p583_1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h575, hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h0, h568, h574, h575, hc01, hlam, hphi, ht12, ht23, p583_1, u3elo1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p583_1, u5elo1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h574, hlam, p583_1]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h576, hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [h577, hlam, p583_0]
                                        · have p583_0 := h583c.1
                                          have p583_1 := h583c.2.1
                                          have p583_2 := h583c.2.2.1
                                          have p583_3 := h583c.2.2.2
                                          linarith only [hlam, p583_0]
                                    · linarith only [h564, h571, h580, hlam]
                                  · linarith only [h426, h570, h571, h579, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi9]
                                · linarith only [h0, h426, h568, h570, h571, h574, h578, hc01, hlam, hphi, ht12, ht23, u3elo3, u5ehi9, u5elo1]
                              · linarith only [h420, h426, h570, h571, h577, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h426, h568, h570, h571, h572, h574, h576, hc01, hlam, hphi, ht12, ht23, u3elo4, u5ehi9, u5elo1]
                          · linarith only [h426, h570, h572, h575, hlam]
                        · linarith only [h0, h426, h570, h571, h572, h574, hc01, hlam, hphi, ht12, ht23, u3elo1, u5ehi9, u5elo2]
                      · linarith only [h426, h570, h571, h572, h573, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h0, h572, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h624 | h624
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h625 | h625
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h626 | h626
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h627 | h627
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h628 | h628
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h629 | h629
                              · linarith only [h0, h564, h571, h627, h629, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · linarith only [h420, h629, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h320, h628, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h426, h624, h627, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h626, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h426, h624, h625, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h624, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h638 | h638
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h639 | h639
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h640 | h640
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h641 | h641
                          · linarith only [h570, h641, hc03, hlam, hphi, u3elo1]
                          · linarith only [h320, h641, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h564, h637, h639, h640, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                      · linarith only [h0, h426, h638, h639, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h638, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h647 | h647
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h648 | h648
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h649 | h649
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h650 | h650
                          · linarith only [h0, h426, h570, h650, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h320, h650, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h426, h647, h649, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h426, h647, h648, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h647, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
