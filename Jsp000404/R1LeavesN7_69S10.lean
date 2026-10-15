import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h0, h10, h11, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h10, h14, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                            · linarith only [h1, h17, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h17, h8, hc13, hlam, hphi, u3elo0]
                          · linarith only [h10, h16, h7, hc12, hlam, hphi, ht23, u3elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h0, h22, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h0, h21, h22, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                        · linarith only [h21, h25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                            · linarith only [h1, h28, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h28, h8, hc13, hlam, hphi, u3elo0]
                          · linarith only [h21, h27, h7, hc12, hlam, hphi, ht23, u3elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h32, h7, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                        · linarith only [h0, h35, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h0, h34, h35, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h34, h4, h8, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h39 | h39
                  · linarith only [h39, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                        · linarith only [h0, h43, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h0, h42, h43, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h4, h42, h7, hc12, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                        · linarith only [h0, h48, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h0, h47, h48, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h4, h47, h7, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h52 | h52
                · rcases m.htr 0 3 5 (by decide) (by decide) with h53 | h53
                  · linarith only [h4, h53, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h52, h53, h55, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
                        · linarith only [h0, h58, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h61 | h61
                            · linarith only [h53, h61, hc03, hlam, hphi, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h63 | h63
                              · linarith only [h2, h55, h63, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                                · linarith only [h0, h57, h65, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h1, h53, h60, h65, hc23, hlam, hphi, u3elo4]
                          · linarith only [h52, h53, h60, hc13, hlam, hphi, u3elo4]
                      · linarith only [h4, h57, h6, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
                  · linarith only [h52, h70, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h72 | h72
                    · linarith only [h5, h6, h72, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                        · linarith only [h0, h75, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                          · linarith only [h52, h77, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                            · linarith only [h1, h70, h79, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                              · linarith only [h2, h72, h81, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                                · linarith only [h52, h83, hc03, hlam, hphi, u3elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                                  · linarith only [h1, h70, h74, h85, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                  · linarith only [h0, h6, h74, h85, hc23, hlam, hphi, u3elo4]
                      · linarith only [h4, h6, h74, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h89 | h89
              · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
                · linarith only [h4, h5, h90, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h92 | h92
                  · linarith only [h90, h92, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                        · linarith only [h0, h96, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h89, h95, h96, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h4, h5, h90, h95, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h5, h89, h94, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h103 | h103
                  · linarith only [h101, h103, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                        · linarith only [h0, h107, h89, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
                          · linarith only [h1, h101, h109, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
                            · linarith only [h1, h103, h111, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                              · linarith only [h113, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h101, h105, h109, h113, hc13, hlam, hphi, u3elo3]
                      · linarith only [h106, h4, h89, hc12, hc25, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                        · linarith only [h0, h118, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h120 | h120
                          · linarith only [h101, h120, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h122 | h122
                            · linarith only [h1, h103, h122, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                              · linarith only [h105, h124, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                                · linarith only [h0, h101, h117, h126, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h126, h4, h5, hc23, hlam, hphi, u3elo3]
                      · linarith only [h117, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h130 | h130
            · rcases m.htr 0 2 5 (by decide) (by decide) with h131 | h131
              · linarith only [h131, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h133 | h133
                · rcases m.htr 0 3 5 (by decide) (by decide) with h134 | h134
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
                    · linarith only [h130, h135, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                      · linarith only [h0, h137, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
                        · linarith only [h0, h131, h139, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                            · linarith only [h1, h142, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h134, h142, hc13, hlam, hphi, u3elo0]
                          · linarith only [h133, h137, h141, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
                    · linarith only [h130, h134, h146, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                      · linarith only [h0, h134, h148, h4, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                        · linarith only [h130, h131, h148, h150, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                            · linarith only [h1, h134, h153, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                              · linarith only [h146, h155, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                                  · linarith only [h134, h158, hc03, hlam, hphi, u3elo2]
                                  · linarith only [h130, h157, h158, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h130, h152, h157, h2, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h133, h152, hc13, hlam, hphi, u3elo0]
                · linarith only [h130, h133, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h164 | h164
              · linarith only [h164, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h166 | h166
                · rcases m.htr 0 3 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                      · linarith only [h0, h169, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                        · linarith only [h164, h169, h171, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                            · linarith only [h1, h174, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h167, h173, h174, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h166, h173, h4, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                      · linarith only [h0, h167, h178, h4, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h180 | h180
                        · linarith only [h164, h178, h180, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                            · linarith only [h1, h183, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h167, h183, h4, hc13, hlam, hphi, u3elo2]
                          · linarith only [h166, h178, h182, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h187 | h187
                    · linarith only [h166, h167, h187, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
                      · linarith only [h0, h189, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h191 | h191
                        · linarith only [h0, h164, h191, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h193 | h193
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h194 | h194
                            · linarith only [h1, h167, h194, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
                              · linarith only [h1, h130, h167, h187, h193, h196, h2, hc02, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, u0elo0, u3elo4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                                  · linarith only [h1, h167, h193, h199, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · linarith only [h0, h199, h4, hc12, hlam, hphi, ht23, u3elo4]
                                · linarith only [h0, h1, h193, h198, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h166, h167, h193, hc13, hlam, hphi, u3elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h204 | h204
                  · linarith only [h166, h204, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h206 | h206
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h207 | h207
                      · linarith only [h0, h207, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                        · linarith only [h164, h207, h209, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
                          · linarith only [h1, h166, h211, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h213 | h213
                            · linarith only [h1, h204, h213, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h215 | h215
                              · linarith only [h2, h215, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h166, h206, h211, h215, hc13, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
                      · linarith only [h0, h218, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h220 | h220
                        · linarith only [h164, h218, h220, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h222 | h222
                          · linarith only [h1, h166, h222, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h224 | h224
                            · linarith only [h1, h204, h224, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h226 | h226
                              · linarith only [h2, h206, h226, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                                · linarith only [h0, h166, h228, h4, hc12, hlam, hphi, ht23, u3elo2]
                                · linarith only [h0, h228, h4, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h231 | h231
          · rcases m.htr 0 2 4 (by decide) (by decide) with h232 | h232
            · rcases m.htr 0 2 5 (by decide) (by decide) with h233 | h233
              · linarith only [h0, h233, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h235 | h235
                · rcases m.htr 0 3 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h1, h236, h3, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h238 | h238
                    · linarith only [h235, h236, h238, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
                      · linarith only [h0, h236, h240, h3, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h231, h236, h240, h3, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h243 | h243
                  · linarith only [h235, h243, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h245 | h245
                    · linarith only [h2, h245, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
                      · linarith only [h0, h243, h247, h3, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h231, h243, h247, h3, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h250 | h250
              · linarith only [h2, h232, h250, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
                · linarith only [h231, h232, h252, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h254 | h254
                  · linarith only [h252, h254, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h256 | h256
                    · linarith only [h2, h256, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                      · linarith only [h0, h254, h258, h3, hc23, hlam, hphi, u3elo4]
                      · linarith only [h231, h232, h256, h258, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h261 | h261
            · rcases m.htr 0 2 5 (by decide) (by decide) with h262 | h262
              · linarith only [h231, h262, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h264 | h264
                · rcases m.htr 0 3 5 (by decide) (by decide) with h265 | h265
                  · linarith only [h1, h265, h3, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
                    · linarith only [h231, h261, h265, h267, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                      · linarith only [h0, h231, h265, h269, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                        · linarith only [h0, h231, h262, h271, h3, hc01, hlam, hphi, ht12, ht23, u3elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
                            · linarith only [h1, h231, h265, h274, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h1, h273, h274, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h264, h265, h269, h273, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h231, h261, h264, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h279 | h279
              · linarith only [h231, h279, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h281 | h281
                · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
                  · linarith only [h1, h282, h3, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
                    · linarith only [h281, h282, h284, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h286 | h286
                      · linarith only [h0, h261, h281, h282, h286, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
                        · linarith only [h1, h279, h286, h288, h3, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h290 | h290
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h291 | h291
                            · linarith only [h1, h261, h281, h282, h291, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h1, h290, h291, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h281, h282, h286, h290, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h295 | h295
                  · linarith only [h281, h295, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h297 | h297
                    · linarith only [h2, h297, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
                      · linarith only [h0, h231, h299, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h301 | h301
                        · linarith only [h0, h231, h301, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h303 | h303
                          · linarith only [h1, h231, h281, h303, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h305 | h305
                            · linarith only [h1, h281, h295, h305, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                            · linarith only [h2, h3, h303, h305, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h308 | h308
        · rcases m.htr 0 2 3 (by decide) (by decide) with h309 | h309
          · rcases m.htr 0 2 4 (by decide) (by decide) with h310 | h310
            · linarith only [h0, h2, h310, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h312 | h312
              · rcases m.htr 0 3 4 (by decide) (by decide) with h313 | h313
                · linarith only [h1, h2, h313, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h315 | h315
                  · linarith only [h313, h315, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
                      · linarith only [h0, h2, h313, h318, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h2, h309, h313, h318, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h0, h2, h312, h317, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h322 | h322
                · linarith only [h1, h2, h322, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h324 | h324
                  · linarith only [h322, h324, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
                      · linarith only [h0, h2, h322, h327, hc23, hlam, hphi, u3elo3]
                      · linarith only [h2, h308, h309, h312, h322, h327, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h2, h308, h326, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h331 | h331
            · linarith only [h0, h2, h331, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h333 | h333
              · linarith only [h309, h333, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h335 | h335
                · linarith only [h1, h2, h335, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h337 | h337
                  · linarith only [h335, h337, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                      · linarith only [h0, h309, h335, h340, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                        · linarith only [h0, h333, h342, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                          · linarith only [h1, h2, h335, h344, hlam]
                          · linarith only [h2, h308, h344, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi1]
                    · linarith only [h2, h308, h339, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h348 | h348
          · rcases m.htr 0 2 4 (by decide) (by decide) with h349 | h349
            · linarith only [h0, h2, h349, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h351 | h351
              · linarith only [h0, h308, h351, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h353 | h353
                · linarith only [h1, h2, h353, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h355 | h355
                  · linarith only [h353, h355, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h357 | h357
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
                      · linarith only [h0, h308, h353, h357, h358, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h308, h348, h353, h357, h358, hc12, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h361 | h361
                      · linarith only [h0, h2, h355, h357, h361, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h2, h348, h355, h357, h361, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h364 | h364
            · linarith only [h0, h2, h364, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h366 | h366
              · linarith only [h348, h366, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h368 | h368
                · linarith only [h1, h2, h368, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h370 | h370
                  · linarith only [h368, h370, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h372 | h372
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                      · linarith only [h0, h348, h368, h373, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h375 | h375
                        · linarith only [h0, h308, h366, h375, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h377 | h377
                          · linarith only [h1, h348, h368, h377, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h2, h377, hc12, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h380 | h380
                      · linarith only [h0, h348, h380, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h382 | h382
                        · linarith only [h1, h380, h382, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                          · linarith only [h1, h2, h348, h368, h370, h372, h384, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h0, h2, h384, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h388 | h388
    · rcases m.htr 0 1 4 (by decide) (by decide) with h389 | h389
      · rcases m.htr 0 1 5 (by decide) (by decide) with h390 | h390
        · rcases m.htr 0 2 3 (by decide) (by decide) with h391 | h391
          · rcases m.htr 0 2 4 (by decide) (by decide) with h392 | h392
            · rcases m.htr 0 2 5 (by decide) (by decide) with h393 | h393
              · rcases m.htr 0 3 4 (by decide) (by decide) with h394 | h394
                · rcases m.htr 0 3 5 (by decide) (by decide) with h395 | h395
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h396 | h396
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h397 | h397
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h400 | h400
                            · linarith only [h388, h400, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h395, h400, hc13, hlam, hphi, u3elo0]
                          · linarith only [h394, h397, h399, hc23, hlam, hphi, u3elo0]
                        · linarith only [h0, h388, h395, h398, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h388, h394, h396, h397, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h407 | h407
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                            · linarith only [h388, h409, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h395, h408, h409, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · linarith only [h394, h408, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h388, h395, h407, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h388, h395, h406, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h415 | h415
                    · linarith only [h394, h395, h415, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h418 | h418
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h419 | h419
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h420 | h420
                            · linarith only [h388, h395, h420, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h422 | h422
                              · linarith only [h0, h389, h415, h422, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h424 | h424
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h425 | h425
                                  · linarith only [h388, h395, h417, h425, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h427 | h427
                                    · linarith only [h389, h415, h419, h427, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                    · rcases h0bigk with h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [hlam, p429_0]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h0, hlam, p429_1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h0, h388, h417, h424, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p429_1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        rcases p429_3 (m.d 0 1) (by simp) with h433 | h433
                                        · rcases p429_3 (m.d 0 2) (by simp) with h434 | h434
                                          · rcases p429_3 (m.d 0 3) (by simp) with h435 | h435
                                            · linarith only [h388, h435, hlam]
                                            · linarith only [h394, h435, hlam]
                                          · linarith only [h392, h434, hlam]
                                        · linarith only [h389, h433, hlam]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h0, h388, h395, h417, h424, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p429_1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h388, h417, h424, hc34, hlam, hphi, ht0b, ht45, ht5b, p429_1, u0elo1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [hlam, p429_0]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h388, h417, h424, hc34, hlam, hphi, ht0b, ht45, ht5b, p429_1, u0elo1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        rcases p429_3 (m.d 0 1) (by simp) with h444 | h444
                                        · linarith only [h0, h444, hlam]
                                        · linarith only [h389, h444, hlam]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h388, h395, h417, h424, hc34, hlam, hphi, ht0b, ht45, ht5b, p429_1, u0elo1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h388, hlam, p429_1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h391, hlam, p429_1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [hlam, p429_0]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h392, h395, h424, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p429_1, u3elo4]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h395, hlam, p429_1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h389, hlam, p429_0]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h392, hlam, p429_0]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h394, hlam, p429_0]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [hlam, p429_0]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h415, hlam, p429_0]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h390, hlam, p429_0]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h393, hlam, p429_1]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [h388, h417, h424, hc34, hlam, hphi, ht0b, ht45, ht5b, p429_1, u0elo4]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        rcases p429_3 (m.d 0 1) (by simp) with h461 | h461
                                        · rcases p429_3 (m.d 0 2) (by simp) with h462 | h462
                                          · rcases p429_3 (m.d 0 3) (by simp) with h463 | h463
                                            · linarith only [h395, h463, hlam]
                                            · linarith only [h394, h463, hlam]
                                          · linarith only [h392, h462, hlam]
                                        · linarith only [h389, h461, hlam]
                                      · have p429_0 := h429c.1
                                        have p429_1 := h429c.2.1
                                        have p429_2 := h429c.2.2.1
                                        have p429_3 := h429c.2.2.2
                                        linarith only [hlam, p429_0]
                                · linarith only [h394, h424, hc23, hlam, hphi, u3elo0]
                          · linarith only [h394, h395, h419, hc13, hlam, hphi, u3elo4]
                        · linarith only [h0, h390, h418, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h390, h417, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h473 | h473
                  · linarith only [h394, h473, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h475 | h475
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h476 | h476
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h477 | h477
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h478 | h478
                          · linarith only [h394, h478, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h480 | h480
                            · linarith only [h388, h473, h480, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h482 | h482
                              · linarith only [h0, h389, h482, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h394, h475, h476, h478, h482, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h389, h475, h477, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h389, h475, h476, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h487 | h487
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h488 | h488
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h489 | h489
                          · linarith only [h394, h489, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h491 | h491
                            · linarith only [h388, h473, h491, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h493 | h493
                              · linarith only [h389, h475, h493, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h495 | h495
                                · linarith only [h388, h394, h487, h495, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h497 | h497
                                  · linarith only [h388, h390, h394, h473, h487, h488, h497, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h499 | h499
                                    · linarith only [h389, h475, h489, h499, hc13, hlam, hphi, u3elo3]
                                    · rcases h0bigk with h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        rcases p501_3 (m.d 0 1) (by simp) with h504 | h504
                                        · rcases p501_3 (m.d 0 2) (by simp) with h505 | h505
                                          · rcases p501_3 (m.d 0 3) (by simp) with h506 | h506
                                            · linarith only [h388, h506, hlam]
                                            · rcases p501_3 (m.d 0 4) (by simp) with h508 | h508
                                              · linarith only [h389, h508, hlam]
                                              · linarith only [h394, h508, hlam]
                                          · linarith only [h391, h505, hlam]
                                        · linarith only [h388, h504, hlam]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        rcases p501_3 (m.d 0 1) (by simp) with h513 | h513
                                        · rcases p501_3 (m.d 0 2) (by simp) with h514 | h514
                                          · rcases p501_3 (m.d 0 3) (by simp) with h515 | h515
                                            · linarith only [h388, h515, hlam]
                                            · rcases p501_3 (m.d 0 4) (by simp) with h517 | h517
                                              · linarith only [h389, h517, hlam]
                                              · rcases p501_3 (m.d 0 5) (by simp) with h519 | h519
                                                · linarith only [h390, h519, hlam]
                                                · linarith only [h475, h519, hlam]
                                          · linarith only [h392, h514, hlam]
                                        · linarith only [h389, h513, hlam]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, h390, h488, hc12, hlam, hphi, ht01, ht0b, ht5b, p501_1, u5ehi2]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h388, h487, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p501_1, u0elo1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        rcases p501_3 (m.d 0 1) (by simp) with h527 | h527
                                        · linarith only [h0, h527, hlam]
                                        · linarith only [h388, h527, hlam]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        rcases p501_3 (m.d 0 1) (by simp) with h530 | h530
                                        · linarith only [h0, h530, hlam]
                                        · linarith only [h389, h530, hlam]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h390, h488, hlam, hphi, ht0b, ht5b, p501_1, u0elo1, u5ehi2]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h388, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h391, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h394, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h473, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h389, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h392, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h388, h394, h487, h499, hc23, hc45, hlam, hphi, ht34, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h475, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h390, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h393, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h388, h473, h487, hc23, hlam, hphi, p501_1, u3elo4]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h389, h473, h487, h489, hc23, hlam, hphi, p501_1, u3elo4]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                        · linarith only [h0, h390, h488, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h390, h487, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h390, h393, hlam]
            · linarith only [h0, h389, h392, hlam]
          · linarith only [h0, h390, h391, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h554 | h554
          · rcases m.htr 0 2 4 (by decide) (by decide) with h555 | h555
            · rcases m.htr 0 2 5 (by decide) (by decide) with h556 | h556
              · rcases m.htr 0 3 4 (by decide) (by decide) with h557 | h557
                · rcases m.htr 0 3 5 (by decide) (by decide) with h558 | h558
                  · linarith only [h388, h390, h558, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h560 | h560
                    · linarith only [h557, h558, h560, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h563 | h563
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h564 | h564
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h565 | h565
                            · linarith only [h388, h558, h565, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h388, h390, h564, h565, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h388, h390, h557, h558, h562, h564, hc23, hlam, hphi, u3elo4]
                        · linarith only [h0, h556, h563, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h388, h562, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
                  · linarith only [h557, h571, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
                    · linarith only [h389, h390, h573, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h575 | h575
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h576 | h576
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h577 | h577
                          · linarith only [h557, h577, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h579 | h579
                            · linarith only [h388, h390, h571, h579, hlam]
                            · linarith only [h389, h390, h575, h577, h579, hc23, hlam, hphi, u3elo4]
                        · linarith only [h0, h556, h576, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h388, h575, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h584 | h584
                · rcases m.htr 0 3 5 (by decide) (by decide) with h585 | h585
                  · linarith only [h388, h390, h585, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h587 | h587
                    · linarith only [h584, h585, h587, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h589 | h589
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h590 | h590
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h591 | h591
                          · linarith only [h0, h388, h556, h590, h591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h584, h585, h589, h591, hc23, hlam, hphi, u3elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h594 | h594
                          · linarith only [h0, h388, h590, h594, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h584, h585, h594, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h589, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h598 | h598
                  · linarith only [h584, h598, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h600 | h600
                    · linarith only [h0, h389, h556, h600, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h602 | h602
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h603 | h603
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h604 | h604
                          · linarith only [h584, h604, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h606 | h606
                            · linarith only [h0, h388, h556, h598, h606, hlam]
                            · linarith only [h0, h389, h556, h602, h603, h604, h606, hc23, hlam, hphi, u3elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h609 | h609
                          · linarith only [h584, h609, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
                            · linarith only [h388, h584, h611, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                            · linarith only [h0, h389, h602, h603, h609, h611, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h602, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h0, h389, h555, hlam]
          · linarith only [h0, h388, h554, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h617 | h617
        · rcases m.htr 0 2 3 (by decide) (by decide) with h618 | h618
          · rcases m.htr 0 2 4 (by decide) (by decide) with h619 | h619
            · rcases m.htr 0 2 5 (by decide) (by decide) with h620 | h620
              · rcases m.htr 0 3 4 (by decide) (by decide) with h621 | h621
                · linarith only [h388, h389, h621, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h623 | h623
                  · linarith only [h621, h623, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h625 | h625
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h626 | h626
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h627 | h627
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h628 | h628
                          · linarith only [h388, h621, h628, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h389, h617, h628, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi1]
                        · linarith only [h0, h617, h627, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h617, h626, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h389, h617, h625, hlam]
              · linarith only [h389, h617, h619, h620, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h635 | h635
              · rcases m.htr 0 3 4 (by decide) (by decide) with h636 | h636
                · linarith only [h0, h388, h619, h636, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h638 | h638
                  · linarith only [h636, h638, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h640 | h640
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h641 | h641
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h642 | h642
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h643 | h643
                          · linarith only [h388, h636, h643, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h389, h617, h643, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi1]
                        · linarith only [h0, h617, h642, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h617, h641, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h617, h619, h640, hlam]
              · linarith only [h0, h617, h635, hlam]
          · linarith only [h0, h388, h618, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h651 | h651
          · rcases m.htr 0 2 4 (by decide) (by decide) with h652 | h652
            · rcases m.htr 0 2 5 (by decide) (by decide) with h653 | h653
              · rcases m.htr 0 3 4 (by decide) (by decide) with h654 | h654
                · linarith only [h388, h389, h654, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h656 | h656
                  · linarith only [h654, h656, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h661 | h661
                          · linarith only [h654, h661, hc03, hlam, hphi, u3elo1]
                          · linarith only [h388, h389, h659, h661, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h388, h653, h659, h660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h653, h659, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h667 | h667
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h668 | h668
                          · linarith only [h388, h389, h658, h668, hc34, hc45, hlam, hphi]
                          · linarith only [h388, h389, h668, hc13, hlam, hphi, u3elo3]
                        · linarith only [h0, h388, h653, h666, h667, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h388, h666, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h673 | h673
                · linarith only [h388, h389, h673, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h675 | h675
                  · linarith only [h673, h675, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h677 | h677
                    · linarith only [h652, h653, h677, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h679 | h679
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h680 | h680
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h681 | h681
                          · linarith only [h388, h673, h681, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h388, h389, h679, h681, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h684 | h684
                          · linarith only [h0, h388, h680, h684, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h388, h389, h684, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h388, h679, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h688 | h688
              · rcases m.htr 0 3 4 (by decide) (by decide) with h689 | h689
                · linarith only [h0, h388, h652, h689, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h691 | h691
                  · linarith only [h689, h691, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h693 | h693
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h694 | h694
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h695 | h695
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h696 | h696
                          · linarith only [h689, h696, hc03, hlam, hphi, u3elo1]
                          · linarith only [h388, h389, h694, h696, hc23, hlam, hphi, u3elo3]
                        · linarith only [h652, h688, h689, h695, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h0, h694, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h652, h688, h693, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h702 | h702
                · linarith only [h0, h388, h652, h702, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h704 | h704
                  · linarith only [h702, h704, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h706 | h706
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h707 | h707
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h708 | h708
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h709 | h709
                          · linarith only [h702, h709, hc03, hlam, hphi, u3elo1]
                          · linarith only [h388, h389, h707, h709, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h712 | h712
                          · linarith only [h0, h388, h688, h702, h706, h708, h712, hc02, hc25, hlam, hphi]
                          · linarith only [h388, h389, h707, h712, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h707, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h716 | h716
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h717 | h717
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h718 | h718
                          · linarith only [h0, h388, h652, h702, h718, hlam]
                          · linarith only [h388, h389, h718, hc13, hlam, hphi, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h721 | h721
                          · linarith only [h0, h388, h702, h717, h721, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h388, h389, h716, h721, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h388, h716, hc13, hlam, hphi, u3elo2]
          · linarith only [h0, h388, h651, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h726 | h726
      · rcases m.htr 0 1 5 (by decide) (by decide) with h727 | h727
        · linarith only [h388, h727, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h729 | h729
          · rcases m.htr 0 2 4 (by decide) (by decide) with h730 | h730
            · rcases m.htr 0 2 5 (by decide) (by decide) with h731 | h731
              · rcases m.htr 0 3 4 (by decide) (by decide) with h732 | h732
                · rcases m.htr 0 3 5 (by decide) (by decide) with h733 | h733
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h734 | h734
                    · linarith only [h388, h726, h734, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h736 | h736
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h737 | h737
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h738 | h738
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h739 | h739
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h740 | h740
                              · linarith only [h726, h727, h734, h739, h740, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h742 | h742
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h743 | h743
                                  · linarith only [h729, h743, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h733, h743, hc23, hlam, hphi, u3elo0]
                                · linarith only [h726, h727, h738, h739, h742, hc23, hlam, hphi, u3elo1]
                            · linarith only [h388, h733, h739, hlam]
                          · linarith only [h388, h733, h738, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h0, h731, h737, hlam]
                      · linarith only [h0, h731, h736, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h751 | h751
                    · linarith only [h388, h726, h751, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h753 | h753
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h754 | h754
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h755 | h755
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h756 | h756
                            · linarith only [h388, h726, h733, h755, h756, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h388, h726, h755, h756, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h388, h726, h755, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h388, h726, h731, h753, h754, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h731, h753, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                · linarith only [h388, h726, h732, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h763 | h763
                · rcases m.htr 0 3 5 (by decide) (by decide) with h764 | h764
                  · linarith only [h729, h731, h764, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h766 | h766
                    · linarith only [h388, h726, h766, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h768 | h768
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h769 | h769
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h770 | h770
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h771 | h771
                            · linarith only [h388, h726, h764, h770, h771, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h388, h726, h770, h771, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h388, h726, h770, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h775 | h775
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h776 | h776
                            · linarith only [h764, h776, hc03, hlam, hphi, u3elo1]
                            · linarith only [h388, h726, h775, h776, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h388, h726, h775, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h729, h768, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h388, h726, h763, hlam]
            · linarith only [h0, h726, h730, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h783 | h783
            · rcases m.htr 0 2 5 (by decide) (by decide) with h784 | h784
              · linarith only [h729, h784, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h786 | h786
                · rcases m.htr 0 3 5 (by decide) (by decide) with h787 | h787
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h788 | h788
                    · linarith only [h0, h726, h729, h788, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h791 | h791
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h792 | h792
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h793 | h793
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h794 | h794
                              · linarith only [h0, h726, h784, h788, h791, h793, h794, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h796 | h796
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h797 | h797
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h798 | h798
                                    · linarith only [h0, h784, h791, h794, h798, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                    · rcases h0bigk with h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c
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
                                        linarith only [h388, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h0, h726, h784, h791, h792, h794, hc34, hc45, hlam, hphi, p800_1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h727, hlam, p800_1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h784, h791, h793, hc01, hc13, hlam, hphi, p800_1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h729, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h726, h729, h792, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p800_1, u3elo2]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h784, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p800_1, u3elo0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h388, hc02, hlam, hphi, ht23, p800_1, u3elo1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        rcases p800_3 (m.d 0 1) (by simp) with h814 | h814
                                        · linarith only [h388, h814, hlam]
                                        · linarith only [h726, h814, hlam]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h729, h790, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p800_1, u3elo1, u5ehi0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h726, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h783, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h786, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h788, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h726, h792, hc34, hlam, hphi, ht0b, ht45, ht5b, p800_1, u0elo4]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h0, h726, h784, h791, h792, h793, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p800_1, u3elo1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h787, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        rcases p800_3 (m.d 0 1) (by simp) with h826 | h826
                                        · linarith only [h727, h826, hlam]
                                        · linarith only [h726, h826, hlam]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hlam, p800_0]
                                  · linarith only [h0, h726, h729, h792, h797, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h0, h726, h729, h792, h796, hlam]
                            · linarith only [h787, h793, hc13, hlam, hphi, u3elo0]
                          · linarith only [h0, h729, h790, h792, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h726, h729, h790, h791, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h726, h790, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h836 | h836
                    · linarith only [h388, h726, h836, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                            · linarith only [h0, h729, h787, h841, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h388, h726, h840, h841, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h0, h726, h729, h838, h840, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h726, h729, h838, h839, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h726, h838, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h388, h726, h786, hlam]
            · linarith only [h0, h726, h783, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h849 | h849
        · linarith only [h388, h849, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h851 | h851
          · rcases m.htr 0 2 4 (by decide) (by decide) with h852 | h852
            · rcases m.htr 0 2 5 (by decide) (by decide) with h853 | h853
              · rcases m.htr 0 3 4 (by decide) (by decide) with h854 | h854
                · rcases m.htr 0 3 5 (by decide) (by decide) with h855 | h855
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h856 | h856
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h857 | h857
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h858 | h858
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h859 | h859
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h860 | h860
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h861 | h861
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h862 | h862
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h863 | h863
                                  · linarith only [h851, h863, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h855, h862, h863, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · linarith only [h388, h854, h862, hc23, hlam, hphi, u3elo1]
                              · linarith only [h726, h856, h861, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h388, h855, h860, hlam]
                          · linarith only [h388, h854, h859, hlam]
                        · linarith only [h0, h853, h858, hlam]
                      · linarith only [h0, h853, h857, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h872 | h872
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h873 | h873
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h874 | h874
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h875 | h875
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h876 | h876
                              · linarith only [h726, h856, h874, h876, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h878 | h878
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h879 | h879
                                  · linarith only [h851, h879, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h388, h855, h879, hc23, hlam, hphi, u3elo1]
                                · linarith only [h388, h854, h878, hc23, hlam, hphi, u3elo1]
                            · linarith only [h388, h875, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h388, h854, h855, h874, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                        · linarith only [h0, h853, h873, hlam]
                      · linarith only [h0, h851, h855, h872, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h887 | h887
                    · linarith only [h854, h855, h887, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h889 | h889
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h890 | h890
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h891 | h891
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h892 | h892
                            · linarith only [h855, h892, hc03, hlam, hphi, u3elo1]
                            · linarith only [h388, h892, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h388, h854, h891, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h853, h890, hlam]
                      · linarith only [h0, h851, h889, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h898 | h898
                  · linarith only [h854, h898, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h901 | h901
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h902 | h902
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
                          · linarith only [h854, h903, hc03, hlam, hphi, u3elo1]
                          · linarith only [h388, h903, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h853, h902, hlam]
                      · linarith only [h0, h851, h852, h900, h901, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h908 | h908
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h909 | h909
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h910 | h910
                          · linarith only [h854, h910, hc03, hlam, hphi, u3elo1]
                          · linarith only [h388, h910, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h853, h909, hlam]
                      · linarith only [h0, h851, h853, h908, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h915 | h915
                · rcases m.htr 0 3 5 (by decide) (by decide) with h916 | h916
                  · linarith only [h851, h853, h916, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h918 | h918
                    · linarith only [h915, h916, h918, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h920 | h920
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h921 | h921
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h922 | h922
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h923 | h923
                            · linarith only [h916, h923, hc03, hlam, hphi, u3elo1]
                            · linarith only [h388, h923, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h388, h915, h922, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h927 | h927
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h928 | h928
                            · linarith only [h916, h928, hc03, hlam, hphi, u3elo1]
                            · linarith only [h388, h928, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h388, h915, h927, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h851, h920, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h933 | h933
                  · linarith only [h915, h933, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h935 | h935
                    · linarith only [h852, h853, h935, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h937 | h937
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h938 | h938
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h939 | h939
                          · linarith only [h915, h939, hc03, hlam, hphi, u3elo1]
                          · linarith only [h388, h939, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
                          · linarith only [h388, h915, h937, h938, h942, hc01, hc25, hlam, hphi, ht12]
                          · linarith only [h388, h942, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h937, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h946 | h946
              · rcases m.htr 0 3 4 (by decide) (by decide) with h947 | h947
                · linarith only [h851, h852, h947, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h949 | h949
                  · linarith only [h947, h949, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h951 | h951
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h952 | h952
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h953 | h953
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h954 | h954
                          · linarith only [h388, h947, h954, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h388, h954, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h946, h953, hlam]
                      · linarith only [h0, h851, h946, h952, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
                    · linarith only [h852, h946, h951, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h960 | h960
                · linarith only [h851, h852, h960, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h962 | h962
                  · linarith only [h960, h962, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h964 | h964
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h965 | h965
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h966 | h966
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h967 | h967
                          · linarith only [h960, h967, hc03, hlam, hphi, u3elo1]
                          · linarith only [h388, h967, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h970 | h970
                          · linarith only [h960, h964, h970, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                          · linarith only [h388, h970, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h851, h852, h965, hc12, hc24, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h974 | h974
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h975 | h975
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h976 | h976
                          · linarith only [h388, h960, h976, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h388, h976, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h979 | h979
                          · linarith only [h388, h960, h974, h975, h979, hc01, hc25, hlam, hphi, ht12]
                          · linarith only [h388, h979, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h851, h974, hc01, hlam, hphi, ht12, ht23, u3elo0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h983 | h983
            · rcases m.htr 0 2 5 (by decide) (by decide) with h984 | h984
              · linarith only [h851, h984, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h986 | h986
                · rcases m.htr 0 3 5 (by decide) (by decide) with h987 | h987
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h988 | h988
                    · linarith only [h851, h983, h988, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h990 | h990
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h991 | h991
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h992 | h992
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h993 | h993
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h994 | h994
                              · linarith only [h726, h988, h992, h994, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h996 | h996
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h997 | h997
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h998 | h998
                                    · linarith only [h983, h994, h996, h998, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases h0bigk with h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h0, hlam, p1000_1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h388, hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h726, hlam, p1000_1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h849, hlam, p1000_1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h984, h991, h993, hc01, hlam, hphi, ht12, ht23, p1000_1, u3elo1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h851, hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h726, h984, h991, h993, hc01, hlam, hphi, ht12, ht23, p1000_1, u3elo1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h984, hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h851, h990, hc01, hlam, hphi, ht12, ht23, p1000_1, u3elo1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h851, h990, hc02, hlam, hphi, ht23, p1000_1, u3elo1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h726, h851, h990, hc01, hlam, hphi, ht12, ht23, p1000_1, u3elo1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h851, h990, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1000_1, u3elo1, u5ehi0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h726, h994, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1000_1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h983, hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h986, hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h988, hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h849, h993, hc01, hlam, hphi, ht12, ht23, p1000_1, u3elo1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h983, h984, h991, h993, h996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1000_1, u3elo1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h987, hlam, p1000_0]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [h726, h984, h991, h993, hc01, hlam, hphi, ht12, ht23, p1000_1, u3elo1]
                                      · have p1000_0 := h1000c.1
                                        have p1000_1 := h1000c.2.1
                                        have p1000_2 := h1000c.2.2.1
                                        have p1000_3 := h1000c.2.2.2
                                        linarith only [hlam, p1000_0]
                                  · linarith only [h851, h983, h996, h997, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h851, h983, h996, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h987, h993, hc13, hlam, hphi, u3elo0]
                          · linarith only [h851, h987, h990, h992, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h851, h987, h990, h991, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h990, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1032 | h1032
                    · linarith only [h1032, h851, h983, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1034 | h1034
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1035 | h1035
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1036 | h1036
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1037 | h1037
                            · linarith only [h1037, h851, h987, hc02, hlam, hphi, ht23, u3elo1]
                            · linarith only [h1037, h388, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1034, h1036, h851, h983, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h1034, h1035, h851, h983, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1034, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h851, h983, h986, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1044 | h1044
              · linarith only [h1044, h851, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1046 | h1046
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1047 | h1047
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1048 | h1048
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1049 | h1049
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1050 | h1050
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1051 | h1051
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1052 | h1052
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1053 | h1053
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1054 | h1054
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1055 | h1055
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1056 | h1056
                                    · linarith only [h1046, h1056, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · rcases h0bigk with h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [hlam, p1058_0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h0, hlam, p1058_1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h388, hlam, p1058_0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h726, hlam, p1058_1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h849, hlam, p1058_1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1044, h1050, h1051, h1053, hc01, hlam, hphi, ht12, ht23, p1058_1, u3elo1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [hlam, p1058_0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h851, hlam, p1058_0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h983, hlam, p1058_1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1044, hlam, p1058_0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1049, h851, hc01, hlam, hphi, ht12, ht23, p1058_1, u3elo1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1049, h851, hc02, hlam, hphi, ht23, p1058_1, u3elo1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [hlam, p1058_0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1048, h1049, h1056, h851, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1058_1, u3elo1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1049, h851, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1058_1, u3elo1, u5ehi0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1051, h726, hc01, hlam, hphi, ht12, ht23, p1058_1, u3elo1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h0, h1051, h726, hc01, hlam, hphi, ht12, ht23, p1058_1, u3elo1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1046, hlam, p1058_0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [hlam, p1058_0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1046, h1047, h1049, h851, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1058_1, u3elo1, u5ehi3]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1051, h1053, h849, hc01, hlam, hphi, ht12, ht23, p1058_1, u3elo1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h0, h1044, h1050, h1051, h1053, hc01, hlam, hphi, ht12, ht23, p1058_1, u3elo1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1047, hlam, p1058_0]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [h1048, hlam, p1058_1]
                                      · have p1058_0 := h1058c.1
                                        have p1058_1 := h1058c.2.1
                                        have p1058_2 := h1058c.2.2.1
                                        have p1058_3 := h1058c.2.2.2
                                        linarith only [hlam, p1058_0]
                                  · linarith only [h0, h1055, h851, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h1046, h1048, h1054, h851, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                              · linarith only [h1046, h1048, h1053, h726, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1046, h1048, h1049, h1052, h851, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                          · linarith only [h1046, h1049, h1051, h851, hlam]
                        · linarith only [h1046, h1048, h1049, h1050, h851, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1049, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1091 | h1091
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1092 | h1092
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1093 | h1093
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1094 | h1094
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1095 | h1095
                              · linarith only [h1048, h1093, h1095, h726, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1097 | h1097
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1098 | h1098
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1099 | h1099
                                    · linarith only [h1046, h1095, h1099, h726, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                    · rcases h0bigk with h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h0, hlam, p1101_1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h388, hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h726, hlam, p1101_1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h849, hlam, p1101_1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h983, hc01, hc24, hlam, hphi, ht12, p1101_1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h851, hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h983, hlam, p1101_1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1044, hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1091, h851, hc01, hlam, hphi, ht12, ht23, p1101_1, u3elo1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1091, h851, hc02, hlam, hphi, ht23, p1101_1, u3elo1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1091, h726, h851, hc01, hlam, hphi, ht12, ht23, p1101_1, u3elo1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1091, h851, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1101_1, u3elo1, u5ehi0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1095, h726, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1101_1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h0, h1095, h726, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1101_1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1046, hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1048, hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1047, h1091, h851, hc01, hlam, hphi, ht12, ht23, p1101_1, u3elo1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h0, h1047, h1091, h851, hc01, hlam, hphi, ht12, ht23, p1101_1, u3elo1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1047, hlam, p1101_0]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [h1047, h1091, h726, h851, hc01, hlam, hphi, ht12, ht23, p1101_1, u3elo1]
                                      · have p1101_0 := h1101c.1
                                        have p1101_1 := h1101c.2.1
                                        have p1101_2 := h1101c.2.2.1
                                        have p1101_3 := h1101c.2.2.2
                                        linarith only [hlam, p1101_0]
                                  · linarith only [h1047, h1098, h851, hlam]
                                · linarith only [h1047, h1097, h851, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                            · linarith only [h1047, h1091, h1094, h851, hlam]
                          · linarith only [h1046, h1091, h1093, h851, hlam]
                        · linarith only [h1047, h1091, h1092, h851, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h1091, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1133 | h1133
                    · linarith only [h1046, h1047, h1133, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1135 | h1135
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1136 | h1136
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1137 | h1137
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1138 | h1138
                            · linarith only [h1047, h1138, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1138, h388, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h1046, h1135, h1137, h851, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1135, h1136, h851, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1135, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1144 | h1144
                  · linarith only [h1046, h1144, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1146 | h1146
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1147 | h1147
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1148 | h1148
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1149 | h1149
                          · linarith only [h1046, h1149, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1149, h388, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1147, h1148, h851, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1147, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1154 | h1154
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1155 | h1155
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1156 | h1156
                          · linarith only [h0, h1046, h1156, h851, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1156, h388, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1154, h1155, h851, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1154, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
