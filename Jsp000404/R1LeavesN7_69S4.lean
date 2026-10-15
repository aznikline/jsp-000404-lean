import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_0_L_0_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                        · linarith only [h11, h5, hc12, hlam, hphi, u2elo0]
                      · linarith only [h10, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h16, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                        · linarith only [h16, h5, hc12, hlam, hphi, u2elo0]
                      · linarith only [h15, h4, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h0, h22, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                        · linarith only [h22, h5, hc12, hlam, hphi, u2elo0]
                      · linarith only [h20, h21, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h20, h27, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                        · linarith only [h27, h5, hc12, hlam, hphi, u2elo0]
                      · linarith only [h26, h4, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h31, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                        · linarith only [h0, h35, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                        · linarith only [h35, h5, hc12, hlam, hphi, u2elo0]
                      · linarith only [h33, h34, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                        · linarith only [h33, h40, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                        · linarith only [h40, h5, hc12, hlam, hphi, u2elo0]
                      · linarith only [h39, h4, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
                · rcases m.htr 0 4 5 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                        · linarith only [h0, h48, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                        · linarith only [h48, h5, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h46, h47, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                        · linarith only [h46, h53, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                        · linarith only [h5, h53, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h52, hc12, hlam, hphi, u2elo0]
                  · linarith only [h44, h45, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                        · linarith only [h0, h61, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                        · linarith only [h5, h61, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h59, h60, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
                        · linarith only [h59, h66, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                        · linarith only [h5, h66, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h65, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
                        · linarith only [h0, h72, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                        · linarith only [h5, h72, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h70, h71, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
                        · linarith only [h70, h77, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                        · linarith only [h5, h77, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h76, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h81 | h81
              · rcases m.htr 0 3 5 (by decide) (by decide) with h82 | h82
                · rcases m.htr 0 4 5 (by decide) (by decide) with h83 | h83
                  · linarith only [h4, h5, h83, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                        · linarith only [h5, h87, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                            · linarith only [h1, h90, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · linarith only [h1, h82, h89, h90, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h93 | h93
                            · linarith only [h4, h81, h89, h93, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                              · linarith only [h2, h95, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                                · linarith only [h85, h89, h97, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
                                  · linarith only [h4, h5, h81, h85, h87, h89, h93, h99, hc12, hlam, hphi, u2elo4]
                                  · linarith only [h1, h4, h5, h81, h82, h85, h89, h99, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h4, h5, h85, h86, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                        · linarith only [h104, h5, h85, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                            · linarith only [h1, h107, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · linarith only [h1, h106, h107, h82, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h1, h103, h106, h81, h85, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h103, h4, h5, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h112 | h112
                  · linarith only [h112, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                        · linarith only [h0, h116, h5, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                            · linarith only [h1, h119, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                              · linarith only [h0, h112, h114, h118, h121, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                                · linarith only [h0, h114, h123, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h123, h81, h82, hc23, hc35, hlam, hphi]
                          · linarith only [h118, h81, h82, hc13, hc35, hlam, hphi]
                      · linarith only [h115, h4, h5, hc12, hlam, hphi, u2elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                        · linarith only [h114, h129, h5, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h132 | h132
                            · linarith only [h1, h132, h82, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h134 | h134
                              · linarith only [h134, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h137 | h137
                                  · linarith only [h137, h81, h82, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
                                    · linarith only [h112, h139, h4, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                                      · linarith only [h136, h139, h141, h5, hc02, hlam, hphi, u2elo3]
                                      · linarith only [h114, h128, h136, h137, h141, hc34, hc45, hlam, hphi]
                                · linarith only [h114, h128, h136, h81, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h131, h81, h82, hc13, hc35, hlam, hphi]
                      · linarith only [h128, h4, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h147 | h147
                · linarith only [h147, h4, h5, h81, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h149 | h149
                  · linarith only [h149, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                        · linarith only [h153, h5, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                          · linarith only [h1, h155, h81, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                            · linarith only [h1, h147, h157, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                              · linarith only [h0, h149, h152, h159, h81, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                                · linarith only [h1, h151, h161, h81, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                                  · linarith only [h1, h147, h151, h163, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h165 | h165
                                    · linarith only [h149, h152, h165, h81, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                                      · linarith only [h0, h151, h165, h167, h5, hc23, hc34, hlam, hphi]
                                      · rcases h4bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h4, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p169_1, u2elo4]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h161, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u2elo4]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h81, hlam, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h149, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h2, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h161, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p169_1, u1elo0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h155, hlam, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h159, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h4, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h152, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h161, hlam, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h165, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h167, hc04, hc45, hlam, hphi, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h152, h161, h167, hc23, hc45, hlam, hphi, ht34, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h161, h167, hc23, hc45, hlam, hphi, ht34, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h167, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          rcases p169_3 (m.d 0 4) (by simp) with h190 | h190
                                          · linarith only [h190, hlam, p169_0]
                                          · rcases p169_3 (m.d 1 4) (by simp) with h192 | h192
                                            · linarith only [h159, h192, hlam]
                                            · rcases p169_3 (m.d 2 4) (by simp) with h194 | h194
                                              · linarith only [h165, h194, hlam]
                                              · rcases p169_3 (m.d 3 4) (by simp) with h196 | h196
                                                · linarith only [h167, h196, hlam]
                                                · linarith only [h196, h81, hlam]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          rcases p169_3 (m.d 0 4) (by simp) with h199 | h199
                                          · linarith only [h149, h199, hlam]
                                          · linarith only [h199, h2, hlam]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          rcases p169_3 (m.d 0 4) (by simp) with h202 | h202
                                          · linarith only [h149, h202, hlam]
                                          · linarith only [h202, h4, hlam]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h1, h151, h81, hc23, hc45, hlam, hphi, ht34, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                      · linarith only [h152, h4, h5, hc12, hlam, hphi, u2elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                        · linarith only [h151, h209, h5, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
                          · linarith only [h1, h211, h81, hlam]
                          · linarith only [h151, h208, h211, hlam]
                      · linarith only [h208, h4, h5, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h215 | h215
            · linarith only [h215, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
              · rcases m.htr 0 3 5 (by decide) (by decide) with h218 | h218
                · rcases m.htr 0 4 5 (by decide) (by decide) with h219 | h219
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
                      · linarith only [h221, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                        · linarith only [h0, h215, h223, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                          · linarith only [h220, h221, h225, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
                            · linarith only [h1, h217, h225, h227, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
                              · linarith only [h2, h229, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                              · linarith only [h2, h219, h220, h221, h229, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h232 | h232
                      · linarith only [h219, h232, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                        · linarith only [h0, h215, h234, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                            · linarith only [h1, h237, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · linarith only [h1, h218, h236, h237, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
                            · linarith only [h1, h217, h236, h240, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                              · linarith only [h2, h242, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                              · linarith only [h219, h232, h242, h4, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h246 | h246
                      · linarith only [h0, h246, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h248 | h248
                        · linarith only [h0, h215, h248, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                          · linarith only [h245, h246, h250, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h252 | h252
                            · linarith only [h1, h252, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h254 | h254
                              · linarith only [h2, h219, h254, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                                · linarith only [h245, h250, h256, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · linarith only [h217, h256, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h259 | h259
                      · linarith only [h0, h259, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h261 | h261
                        · linarith only [h215, h245, h261, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h263 | h263
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h264 | h264
                            · linarith only [h1, h264, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · linarith only [h1, h218, h263, h264, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                            · linarith only [h1, h217, h263, h267, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                              · linarith only [h217, h219, h245, h263, h269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h271 | h271
                                · linarith only [h245, h263, h271, hc12, hlam, hphi, u2elo2]
                                · linarith only [h217, h219, h245, h271, hc12, hc45, hlam, hphi, ht23, ht34]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h274 | h274
                  · linarith only [h217, h218, h274, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
                      · linarith only [h0, h277, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
                        · linarith only [h0, h215, h279, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
                          · linarith only [h276, h277, h281, hlam]
                          · linarith only [h217, h218, h281, hc13, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h284 | h284
                      · linarith only [h0, h284, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
                        · linarith only [h215, h276, h286, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
                            · linarith only [h1, h218, h289, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h291 | h291
                              · linarith only [h274, h288, h289, h291, h3, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h293 | h293
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h294 | h294
                                  · linarith only [h217, h218, h294, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h296 | h296
                                    · linarith only [h274, h293, h294, h296, h4, hc02, hc35, hlam, hphi, ht23]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h298 | h298
                                      · linarith only [h288, h296, h298, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                      · rcases h4bigk with h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h217, h218, h288, h298, hc34, hc45, hlam, hphi, p300_1]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h4, hlam, p300_1]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h217, h218, h298, hc34, hc45, hlam, hphi, p300_1]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h274, hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h2, hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h284, hlam, p300_1]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p300_1, u1elo0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h291, hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h0, h4, hc12, hlam, hphi, p300_1, u2elo3]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h284, hc12, hlam, hphi, p300_1, u2elo3]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h293, h294, h298, hc34, hc45, hlam, hphi, p300_1]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h296, hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h217, hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h288, hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h293, hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h298, hlam, p300_0]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          rcases p300_3 (m.d 0 4) (by simp) with h321 | h321
                                          · linarith only [h321, hlam, p300_0]
                                          · rcases p300_3 (m.d 1 4) (by simp) with h323 | h323
                                            · linarith only [h291, h323, hlam]
                                            · rcases p300_3 (m.d 2 4) (by simp) with h325 | h325
                                              · linarith only [h296, h325, hlam]
                                              · linarith only [h325, h4, hlam]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          rcases p300_3 (m.d 0 4) (by simp) with h328 | h328
                                          · linarith only [h274, h328, hlam]
                                          · linarith only [h2, h328, hlam]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p300_1]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          rcases p300_3 (m.d 0 4) (by simp) with h332 | h332
                                          · linarith only [h274, h332, hlam]
                                          · linarith only [h217, h332, hlam]
                                        · have p300_0 := h300c.1
                                          have p300_1 := h300c.2.1
                                          have p300_2 := h300c.2.2.1
                                          have p300_3 := h300c.2.2.2
                                          linarith only [hlam, p300_0]
                                · linarith only [h1, h288, h293, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h215, h217, h218, h276, h288, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h338 | h338
                · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                      · linarith only [h0, h341, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h343 | h343
                        · linarith only [h0, h343, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
                          · linarith only [h217, h338, h345, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h347 | h347
                            · linarith only [h0, h340, h347, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                            · linarith only [h217, h338, h347, hc13, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                      · linarith only [h0, h350, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h352 | h352
                        · linarith only [h0, h215, h352, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h354 | h354
                          · linarith only [h217, h338, h354, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
                            · linarith only [h2, h354, h356, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · linarith only [h217, h338, h356, hc13, hc34, hlam, hphi]
                  · linarith only [h217, h338, h339, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h361 | h361
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h362 | h362
                      · linarith only [h0, h362, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h364 | h364
                        · linarith only [h0, h215, h364, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h366 | h366
                          · linarith only [h1, h217, h366, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h368 | h368
                            · linarith only [h1, h338, h368, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                              · linarith only [h2, h370, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                              · linarith only [h360, h362, h370, h4, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h373 | h373
                      · linarith only [h0, h373, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h375 | h375
                        · linarith only [h0, h215, h375, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h377 | h377
                          · linarith only [h1, h217, h377, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h379 | h379
                            · linarith only [h1, h338, h379, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h381 | h381
                              · linarith only [h2, h381, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                              · linarith only [h360, h373, h381, h4, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                      · linarith only [h0, h385, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
                        · linarith only [h0, h215, h387, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h389 | h389
                          · linarith only [h1, h2, h217, h384, h385, h389, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                            · linarith only [h1, h338, h391, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                              · linarith only [h2, h393, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h395 | h395
                                · linarith only [h217, h384, h395, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h397 | h397
                                  · linarith only [h1, h338, h384, h397, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h399 | h399
                                    · linarith only [h360, h399, h4, hc02, hlam, hphi, u2elo3]
                                    · linarith only [h0, h384, h399, h4, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
                      · linarith only [h384, h4, h402, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                        · linarith only [h0, h215, h404, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                          · linarith only [h1, h217, h406, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h408 | h408
                            · linarith only [h1, h408, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                              · linarith only [h2, h217, h360, h410, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                                · linarith only [h1, h217, h384, h412, hc12, hlam, hphi, u2elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h414 | h414
                                  · linarith only [h1, h338, h384, h414, hc12, hlam, hphi, u2elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h416 | h416
                                    · linarith only [h1, h217, h360, h384, h416, hc12, hlam, hphi, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h418 | h418
                                      · linarith only [h0, h4, h416, h418, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h384, h412, h418, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h421 | h421
          · rcases m.htr 0 2 5 (by decide) (by decide) with h422 | h422
            · linarith only [h0, h3, h422, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h424 | h424
              · rcases m.htr 0 3 5 (by decide) (by decide) with h425 | h425
                · linarith only [h1, h3, h425, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                  · linarith only [h2, h3, h427, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h429 | h429
                    · linarith only [h0, h3, h429, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h431 | h431
                      · linarith only [h1, h3, h429, h431, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · linarith only [h421, h422, h431, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h434 | h434
                · linarith only [h421, h422, h424, h434, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
                  · linarith only [h421, h422, h436, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h438 | h438
                    · linarith only [h0, h3, h438, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h440 | h440
                      · linarith only [h1, h3, h438, h440, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · linarith only [h421, h422, h440, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h443 | h443
            · linarith only [h421, h443, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h445 | h445
              · rcases m.htr 0 3 5 (by decide) (by decide) with h446 | h446
                · linarith only [h1, h3, h446, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h448 | h448
                  · linarith only [h1, h3, h445, h448, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
                    · linarith only [h0, h3, h450, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
                      · linarith only [h1, h3, h450, h452, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h454 | h454
                        · linarith only [h1, h3, h443, h450, h454, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                        · linarith only [h1, h3, h450, h454, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h457 | h457
                · linarith only [h2, h3, h445, h457, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
                  · linarith only [h2, h3, h459, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
                    · linarith only [h0, h3, h461, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h463 | h463
                      · linarith only [h0, h421, h463, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h465 | h465
                        · linarith only [h1, h3, h461, h465, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                        · linarith only [h1, h3, h461, h465, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h468 | h468
        · linarith only [h2, h468, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h470 | h470
          · linarith only [h0, h2, h470, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h472 | h472
            · linarith only [h0, h2, h472, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h474 | h474
              · linarith only [h1, h2, h474, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h476 | h476
                · linarith only [h1, h2, h476, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
                    · linarith only [h0, h2, h479, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
                      · linarith only [h1, h2, h470, h479, h481, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                      · linarith only [h0, h2, h481, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h484 | h484
                    · linarith only [h0, h2, h484, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h486 | h486
                      · linarith only [h1, h2, h484, h486, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · linarith only [h1, h2, h484, h486, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h489 | h489
      · rcases m.htr 0 1 5 (by decide) (by decide) with h490 | h490
        · linarith only [h1, h490, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h492 | h492
          · rcases m.htr 0 2 5 (by decide) (by decide) with h493 | h493
            · linarith only [h0, h1, h493, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h495 | h495
              · rcases m.htr 0 3 5 (by decide) (by decide) with h496 | h496
                · rcases m.htr 0 4 5 (by decide) (by decide) with h497 | h497
                  · linarith only [h0, h1, h492, h497, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
                    · linarith only [h0, h1, h499, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h499, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h502 | h502
                  · linarith only [h0, h1, h492, h502, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                    · linarith only [h0, h1, h504, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h504, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h1, h492, h495, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h508 | h508
            · linarith only [h1, h489, h492, h508, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h510 | h510
              · rcases m.htr 0 3 5 (by decide) (by decide) with h511 | h511
                · rcases m.htr 0 4 5 (by decide) (by decide) with h512 | h512
                  · linarith only [h1, h489, h512, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h514 | h514
                    · linarith only [h0, h1, h514, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h514, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h517 | h517
                  · linarith only [h1, h489, h517, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h519 | h519
                    · linarith only [h0, h1, h519, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h519, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h489, h510, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h523 | h523
        · linarith only [h1, h523, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h525 | h525
          · linarith only [h0, h489, h525, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h527 | h527
            · linarith only [h0, h1, h527, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h529 | h529
              · rcases m.htr 0 3 5 (by decide) (by decide) with h530 | h530
                · rcases m.htr 0 4 5 (by decide) (by decide) with h531 | h531
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h532 | h532
                    · linarith only [h0, h1, h532, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h532, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                    · linarith only [h0, h1, h535, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h535, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h538 | h538
                  · linarith only [h529, h530, h538, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h540 | h540
                    · linarith only [h0, h1, h540, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h540, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h543 | h543
                · rcases m.htr 0 4 5 (by decide) (by decide) with h544 | h544
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h545 | h545
                    · linarith only [h0, h1, h545, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h545, hc12, hlam, hphi, u2elo2]
                  · linarith only [h529, h543, h544, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h549 | h549
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
                    · linarith only [h0, h1, h550, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h550, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h553 | h553
                    · linarith only [h0, h1, h553, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h553, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h556 | h556
    · rcases m.htr 0 1 4 (by decide) (by decide) with h557 | h557
      · rcases m.htr 0 1 5 (by decide) (by decide) with h558 | h558
        · linarith only [h0, h558, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h560 | h560
          · rcases m.htr 0 2 5 (by decide) (by decide) with h561 | h561
            · rcases m.htr 0 3 4 (by decide) (by decide) with h562 | h562
              · rcases m.htr 0 3 5 (by decide) (by decide) with h563 | h563
                · linarith only [h0, h556, h563, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h565 | h565
                  · linarith only [h0, h556, h562, h565, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h567 | h567
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h568 | h568
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h570 | h570
                          · linarith only [h556, h558, h569, h570, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h556, h558, h562, h569, h570, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h557, h568, h569, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h0, h561, h568, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                    · linarith only [h0, h567, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h576 | h576
                · linarith only [h0, h557, h562, h576, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h578 | h578
                  · linarith only [h0, h557, h578, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h580 | h580
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h581 | h581
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h582 | h582
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h583 | h583
                          · linarith only [h556, h558, h562, h582, h583, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h585 | h585
                            · linarith only [h556, h558, h576, h582, h585, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h587 | h587
                              · linarith only [h557, h558, h562, h578, h582, h587, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h589 | h589
                                · linarith only [h556, h562, h580, h589, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h591 | h591
                                  · linarith only [h558, h580, h585, h591, hc01, hlam, hphi, u1elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h593 | h593
                                    · linarith only [h557, h558, h581, h587, h593, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h595 | h595
                                      · linarith only [h557, h558, h580, h583, h587, h595, hc23, hc34, hlam, hphi]
                                      · rcases h4bigk with h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h557, h558, h580, h582, h583, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p597_1, u1elo1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h557, h558, h582, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p597_1, u2elo1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h562, hlam, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h578, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h557, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h557, h558, h582, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p597_1, u2elo1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h583, hlam, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h587, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h560, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h581, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h589, hlam, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h593, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h595, hc04, hc45, hlam, hphi, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h581, h595, hc24, hc45, hlam, hphi, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h595, hc24, hc45, hlam, hphi, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h595, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          rcases p597_3 (m.d 0 4) (by simp) with h618 | h618
                                          · linarith only [h618, hlam, p597_0]
                                          · rcases p597_3 (m.d 1 4) (by simp) with h620 | h620
                                            · linarith only [h587, h620, hlam]
                                            · rcases p597_3 (m.d 2 4) (by simp) with h622 | h622
                                              · linarith only [h593, h622, hlam]
                                              · rcases p597_3 (m.d 3 4) (by simp) with h624 | h624
                                                · linarith only [h595, h624, hlam]
                                                · linarith only [h562, h624, hlam]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          rcases p597_3 (m.d 0 4) (by simp) with h627 | h627
                                          · linarith only [h578, h627, hlam]
                                          · linarith only [h557, h627, hlam]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          rcases p597_3 (m.d 0 4) (by simp) with h630 | h630
                                          · linarith only [h578, h630, hlam]
                                          · linarith only [h560, h630, hlam]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h556, h562, h580, hc23, hc45, hlam, hphi, ht34, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                        · linarith only [h561, h582, hc12, hlam, hphi, u2elo0]
                      · linarith only [h0, h556, h580, h581, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h580, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h638 | h638
              · rcases m.htr 0 3 5 (by decide) (by decide) with h639 | h639
                · linarith only [h0, h556, h639, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h641 | h641
                  · linarith only [h0, h557, h561, h641, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h644 | h644
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h645 | h645
                        · linarith only [h0, h561, h645, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h556, h643, h645, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h556, h643, h644, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h643, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h650 | h650
                · linarith only [h0, h557, h638, h650, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h652 | h652
                  · linarith only [h0, h557, h561, h652, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h654 | h654
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h655 | h655
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h656 | h656
                        · linarith only [h0, h561, h656, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h556, h654, h656, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h556, h654, h655, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h654, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h0, h557, h560, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h662 | h662
        · linarith only [h0, h662, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h664 | h664
          · rcases m.htr 0 2 5 (by decide) (by decide) with h665 | h665
            · rcases m.htr 0 3 4 (by decide) (by decide) with h666 | h666
              · linarith only [h556, h557, h666, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h668 | h668
                · linarith only [h0, h556, h668, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h670 | h670
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h671 | h671
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h672 | h672
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h673 | h673
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h674 | h674
                          · linarith only [h556, h557, h666, h672, h674, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h676 | h676
                            · linarith only [h556, h662, h668, h676, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h678 | h678
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
                                · linarith only [h662, h674, h678, h679, hc01, hlam, hphi, ht12, u2elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h681 | h681
                                  · linarith only [h556, h662, h671, h676, h681, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h683 | h683
                                    · linarith only [h664, h683, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h685 | h685
                                      · rcases h4bigk with h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h557, hlam, p686_1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          rcases p686_3 (m.d 0 4) (by simp) with h689 | h689
                                          · rcases p686_3 (m.d 1 4) (by simp) with h690 | h690
                                            · rcases p686_3 (m.d 2 4) (by simp) with h691 | h691
                                              · linarith only [h664, h691, hlam]
                                              · rcases p686_3 (m.d 3 4) (by simp) with h693 | h693
                                                · rcases p686_3 (m.d 4 5) (by simp) with h694 | h694
                                                  · linarith only [h670, h694, hlam]
                                                  · linarith only [h683, h694, hlam]
                                                · linarith only [h679, h693, hlam]
                                            · linarith only [h672, h690, hlam]
                                          · linarith only [h664, h689, hlam]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h666, hlam, p686_1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h557, h679, h683, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p686_1, u1elo3]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h556, h557, h671, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p686_1, u1elo3]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          rcases p686_3 (m.d 0 4) (by simp) with h704 | h704
                                          · linarith only [h557, h704, hlam]
                                          · linarith only [h664, h704, hlam]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h674, hlam, p686_1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h672, h679, h683, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p686_1, u2elo1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h664, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h672, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h679, hlam, p686_1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h683, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h670, h679, h683, hc23, hc34, hlam, hphi, p686_1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h556, h557, h671, hc23, hc34, hlam, hphi, p686_1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          rcases p686_3 (m.d 0 4) (by simp) with h716 | h716
                                          · linarith only [h666, h716, hlam]
                                          · linarith only [h664, h716, hlam]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h679, h683, hc23, hc34, hlam, hphi, p686_1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h670, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h678, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h557, h670, h679, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p686_1, u1elo3]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h685, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                      · linarith only [h0, h556, h664, h666, h670, h671, h685, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h0, h556, h557, h664, h670, h671, h678, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h664, h670, h673, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                      · linarith only [h0, h556, h671, h672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h671, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h731 | h731
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h732 | h732
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h734 | h734
                          · linarith only [h556, h557, h666, h732, h734, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h736 | h736
                            · linarith only [h556, h557, h732, h736, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h738 | h738
                              · linarith only [h556, h557, h670, h731, h732, h738, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h556, h557, h731, h738, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h665, h733, hlam]
                      · linarith only [h0, h665, h732, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                    · linarith only [h0, h556, h731, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h744 | h744
              · linarith only [h556, h557, h744, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h746 | h746
                · linarith only [h0, h556, h746, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h748 | h748
                  · linarith only [h664, h665, h748, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h750 | h750
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h751 | h751
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h752 | h752
                        · linarith only [h557, h664, h665, h752, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h556, h750, h752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h556, h664, h750, h751, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h556, h750, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h757 | h757
            · linarith only [h664, h757, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h759 | h759
              · linarith only [h0, h556, h664, h759, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h761 | h761
                · linarith only [h0, h556, h761, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h763 | h763
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h764 | h764
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h765 | h765
                      · linarith only [h0, h664, h765, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h556, h764, h765, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h764, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h769 | h769
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h770 | h770
                      · linarith only [h0, h556, h664, h769, h770, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h556, h769, h770, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h769, hc01, hlam, hphi, ht12, u2elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h774 | h774
      · rcases m.htr 0 1 5 (by decide) (by decide) with h775 | h775
        · linarith only [h0, h775, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h777 | h777
          · rcases m.htr 0 2 5 (by decide) (by decide) with h778 | h778
            · rcases m.htr 0 3 4 (by decide) (by decide) with h779 | h779
              · rcases m.htr 0 3 5 (by decide) (by decide) with h780 | h780
                · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
                  · linarith only [h0, h774, h781, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h785 | h785
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h787 | h787
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h788 | h788
                              · linarith only [h774, h775, h781, h783, h787, h788, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h790 | h790
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h791 | h791
                                  · linarith only [h783, h791, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                  · linarith only [h556, h780, h783, h790, h791, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · linarith only [h774, h775, h783, h786, h787, h790, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h556, h780, h787, hlam]
                          · linarith only [h556, h779, h786, hlam]
                        · linarith only [h556, h774, h778, h783, h785, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h556, h774, h783, h784, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h778, h783, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h800 | h800
                  · linarith only [h0, h774, h800, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h803 | h803
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h804 | h804
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h805 | h805
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h806 | h806
                            · linarith only [h556, h780, h802, h806, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h808 | h808
                              · linarith only [h774, h800, h808, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h810 | h810
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h811 | h811
                                  · linarith only [h556, h774, h802, h803, h806, h810, h811, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h813 | h813
                                    · linarith only [h556, h774, h803, h806, h808, h813, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h815 | h815
                                      · linarith only [h556, h774, h803, h806, h808, h810, h815, hlam]
                                      · linarith only [h556, h774, h803, h806, h810, h815, hc34, hc45, hlam, hphi]
                                · linarith only [h556, h779, h806, h810, hc23, hc35, hlam, hphi]
                          · linarith only [h556, h774, h779, h805, hlam]
                        · linarith only [h0, h778, h804, hlam]
                      · linarith only [h0, h778, h803, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                    · linarith only [h0, h802, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h556, h774, h779, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h824 | h824
              · rcases m.htr 0 3 5 (by decide) (by decide) with h825 | h825
                · rcases m.htr 0 4 5 (by decide) (by decide) with h826 | h826
                  · linarith only [h0, h774, h826, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h828 | h828
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h829 | h829
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h830 | h830
                        · linarith only [h0, h774, h778, h829, h830, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h774, h829, h830, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h556, h774, h828, h829, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h774, h828, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h835 | h835
                  · linarith only [h0, h774, h835, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h837 | h837
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h839 | h839
                        · linarith only [h0, h778, h839, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h774, h838, h839, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h0, h774, h838, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h774, h837, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h556, h774, h824, hlam]
          · linarith only [h0, h774, h777, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h846 | h846
        · linarith only [h0, h846, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h848 | h848
          · rcases m.htr 0 2 5 (by decide) (by decide) with h849 | h849
            · rcases m.htr 0 3 4 (by decide) (by decide) with h850 | h850
              · rcases m.htr 0 3 5 (by decide) (by decide) with h851 | h851
                · rcases m.htr 0 4 5 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h853 | h853
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h854 | h854
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h855 | h855
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h856 | h856
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h857 | h857
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h858 | h858
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h859 | h859
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h860 | h860
                                  · linarith only [h853, h860, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                  · linarith only [h556, h851, h853, h859, h860, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h863 | h863
                                  · linarith only [h556, h850, h853, h859, h863, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h865 | h865
                                    · linarith only [h848, h865, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h867 | h867
                                      · linarith only [h556, h850, h853, h859, h865, h867, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                      · linarith only [h774, h852, h853, h856, h859, h867, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h774, h852, h858, hlam]
                            · linarith only [h556, h851, h857, hlam]
                          · linarith only [h556, h850, h856, hlam]
                        · linarith only [h556, h851, h853, h855, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                      · linarith only [h556, h850, h852, h853, h854, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                    · linarith only [h0, h849, h853, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h876 | h876
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h877 | h877
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h878 | h878
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h879 | h879
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h880 | h880
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h881 | h881
                              · linarith only [h774, h852, h881, hc01, hlam, hphi, u1elo3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h883 | h883
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h884 | h884
                                  · linarith only [h876, h884, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                                  · linarith only [h556, h851, h883, h884, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h887 | h887
                                  · linarith only [h774, h850, h881, h883, h887, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h889 | h889
                                    · linarith only [h848, h881, h889, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h891 | h891
                                      · linarith only [h556, h774, h850, h876, h881, h891, hc01, hlam, hphi, ht12, u2elo1]
                                      · rcases h4bigk with h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h774, hlam, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h774, h881, hc24, hc45, hlam, hphi, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h774, h881, h883, hc23, hc45, hlam, hphi, ht34, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h852, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h881, hc04, hc45, hlam, hphi, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h881, hc24, hc45, hlam, hphi, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h881, h883, hc23, hc45, hlam, hphi, ht34, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h881, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h848, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h877, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h883, hlam, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h889, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h850, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h879, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h774, h850, h881, hc24, hc45, hlam, hphi, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h891, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h850, h883, hc23, hc45, hlam, hphi, ht34, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h774, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          rcases p893_3 (m.d 0 4) (by simp) with h916 | h916
                                          · linarith only [h852, h916, hlam]
                                          · linarith only [h848, h916, hlam]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h883, hc23, hc45, hlam, hphi, ht34, p893_1]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                            · linarith only [h556, h851, h880, hlam]
                          · linarith only [h556, h774, h850, h851, h879, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                        · linarith only [h0, h878, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h556, h851, h876, h877, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                    · linarith only [h0, h876, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
                  · linarith only [h850, h851, h926, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h928 | h928
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h929 | h929
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h930 | h930
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h931 | h931
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h932 | h932
                            · linarith only [h850, h851, h932, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h934 | h934
                              · linarith only [h774, h926, h934, hc01, hlam, hphi, u1elo3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h936 | h936
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h937 | h937
                                  · linarith only [h928, h932, h937, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h939 | h939
                                    · linarith only [h774, h934, h939, hc01, hlam, hphi, ht12, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h941 | h941
                                      · linarith only [h774, h849, h934, h936, h937, h941, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                      · rcases h4bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h774, hlam, p943_1]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h774, h931, h932, h941, hc24, hc45, hlam, hphi, p943_1]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h774, h931, h932, h941, hc34, hc45, hlam, hphi, p943_1]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h926, hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h931, h932, h941, hc04, hc45, hlam, hphi, p943_1]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h931, h932, h941, hc24, hc45, hlam, hphi, p943_1]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h931, h932, h941, hc34, hc45, hlam, hphi, p943_1]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h934, hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h848, hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h929, hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h0, h848, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo1]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h939, hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h850, hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h931, hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h936, hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h941, hlam, p943_0]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          rcases p943_3 (m.d 0 4) (by simp) with h964 | h964
                                          · linarith only [h964, hlam, p943_0]
                                          · rcases p943_3 (m.d 1 4) (by simp) with h966 | h966
                                            · linarith only [h934, h966, hlam]
                                            · linarith only [h774, h966, hlam]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [h774, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p943_1]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          rcases p943_3 (m.d 0 4) (by simp) with h970 | h970
                                          · linarith only [h926, h970, hlam]
                                          · linarith only [h848, h970, hlam]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          rcases p943_3 (m.d 0 4) (by simp) with h973 | h973
                                          · linarith only [h926, h973, hlam]
                                          · linarith only [h850, h973, hlam]
                                        · have p943_0 := h943c.1
                                          have p943_1 := h943c.2.1
                                          have p943_2 := h943c.2.2.1
                                          have p943_3 := h943c.2.2.2
                                          linarith only [hlam, p943_0]
                                · linarith only [h556, h850, h932, h936, hc23, hc35, hlam, hphi]
                          · linarith only [h556, h774, h850, h931, hc01, hlam, hphi, u1elo3]
                        · linarith only [h0, h849, h930, hlam]
                      · linarith only [h0, h848, h929, hlam]
                    · linarith only [h0, h849, h928, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h982 | h982
                · rcases m.htr 0 4 5 (by decide) (by decide) with h983 | h983
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h984 | h984
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h985 | h985
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h986 | h986
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h987 | h987
                          · linarith only [h850, h982, h987, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h989 | h989
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h990 | h990
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h991 | h991
                                · linarith only [h984, h987, h991, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h993 | h993
                                  · linarith only [h848, h991, h993, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                  · linarith only [h556, h982, h987, h993, hc23, hc34, hlam, hphi]
                              · linarith only [h774, h983, h990, hlam]
                            · linarith only [h0, h556, h848, h850, h982, h989, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h848, h850, h982, h986, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                      · linarith only [h0, h848, h985, hlam]
                    · linarith only [h0, h848, h850, h982, h984, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                  · linarith only [h850, h982, h983, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1002 | h1002
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1003 | h1003
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1004 | h1004
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1005 | h1005
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1006 | h1006
                          · linarith only [h1006, h556, h850, hc01, hlam, hphi, u1elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1008 | h1008
                            · linarith only [h1004, h1006, h1008, h556, h982, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1010 | h1010
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1011 | h1011
                                · linarith only [h1003, h1006, h1011, h556, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1013 | h1013
                                  · linarith only [h1008, h1011, h1013, h556, h848, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1015 | h1015
                                    · linarith only [h0, h1015, h848, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1017 | h1017
                                      · rcases h4bigk with h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h774, hlam, p1018_1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          rcases p1018_3 (m.d 0 4) (by simp) with h1021 | h1021
                                          · rcases p1018_3 (m.d 1 4) (by simp) with h1022 | h1022
                                            · rcases p1018_3 (m.d 2 4) (by simp) with h1023 | h1023
                                              · linarith only [h1023, h848, hlam]
                                              · rcases p1018_3 (m.d 3 4) (by simp) with h1025 | h1025
                                                · rcases p1018_3 (m.d 4 5) (by simp) with h1026 | h1026
                                                  · linarith only [h1002, h1026, hlam]
                                                  · linarith only [h1015, h1026, hlam]
                                                · linarith only [h1011, h1025, hlam]
                                            · linarith only [h1004, h1022, hlam]
                                          · linarith only [h1021, h848, hlam]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h850, hlam, p1018_1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1004, h1011, h1015, h774, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1018_1, u2elo1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1002, h1004, hlam, hphi, ht01, ht0b, ht12, ht5b, p1018_1, u2elo1, u5ehi0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          rcases p1018_3 (m.d 0 4) (by simp) with h1036 | h1036
                                          · linarith only [h1036, h774, hlam]
                                          · linarith only [h1036, h848, hlam]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1006, hlam, p1018_1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1004, h1011, h1015, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1018_1, u2elo1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h848, hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1004, hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1011, hlam, p1018_1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1015, hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1002, h1011, h1015, hc23, hc34, hlam, hphi, p1018_1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h774, hc01, hc34, hlam, hphi, ht12, ht23, p1018_1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          rcases p1018_3 (m.d 0 4) (by simp) with h1048 | h1048
                                          · linarith only [h1048, h850, hlam]
                                          · linarith only [h1048, h848, hlam]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1011, h1015, hc23, hc34, hlam, hphi, p1018_1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1002, hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1010, hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h0, h1002, h1011, h848, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1018_1, u2elo1]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [h1017, hlam, p1018_0]
                                        · have p1018_0 := h1018c.1
                                          have p1018_1 := h1018c.2.1
                                          have p1018_2 := h1018c.2.2.1
                                          have p1018_3 := h1018c.2.2.2
                                          linarith only [hlam, p1018_0]
                                      · linarith only [h0, h1002, h1017, h556, h848, h850, hc01, hlam, hphi, ht12, u2elo1]
                              · linarith only [h1002, h1010, h774, hlam]
                        · linarith only [h0, h1002, h1005, h848, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                      · linarith only [h0, h1002, h1004, h848, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                    · linarith only [h0, h1002, h1003, h848, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1063 | h1063
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1064 | h1064
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1065 | h1065
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1066 | h1066
                          · linarith only [h1066, h556, h850, hc01, hlam, hphi, u1elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1068 | h1068
                            · linarith only [h1064, h1066, h1068, h556, h982, hc01, hlam, hphi, u1elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1070 | h1070
                              · linarith only [h1002, h1064, h1070, h774, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1072 | h1072
                                · linarith only [h1063, h1066, h1072, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1074 | h1074
                                  · linarith only [h1068, h1074, h556, hc01, hlam, hphi, ht12, u2elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1076 | h1076
                                    · linarith only [h1070, h1076, h774, hc01, hlam, hphi, ht12, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1078 | h1078
                                      · linarith only [h1070, h1078, h774, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · linarith only [h1066, h1078, h556, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h1065, h849, hlam]
                      · linarith only [h0, h1064, h849, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                    · linarith only [h0, h1063, h849, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1084 | h1084
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1085 | h1085
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1086 | h1086
                  · linarith only [h1086, h848, h849, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1088 | h1088
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1089 | h1089
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1090 | h1090
                        · linarith only [h1090, h848, h849, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h0, h1090, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1085, h1088, h1089, h556, h848, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h0, h1088, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1095 | h1095
                  · linarith only [h1095, h848, h849, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1097 | h1097
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1098 | h1098
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1099 | h1099
                        · linarith only [h1099, h848, h849, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h0, h1099, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1097, h1098, h556, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1097, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1104 | h1104
                · linarith only [h1084, h1104, h848, h849, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1106 | h1106
                  · linarith only [h1106, h848, h849, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1108 | h1108
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1109 | h1109
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1110 | h1110
                        · linarith only [h1110, h848, h849, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h0, h1110, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1108, h1109, h556, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1108, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1115 | h1115
            · linarith only [h1115, h848, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1117 | h1117
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1118 | h1118
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1119 | h1119
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1120 | h1120
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1121 | h1121
                      · linarith only [h1121, h848, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1121, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1120, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1125 | h1125
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1126 | h1126
                      · linarith only [h0, h1126, h848, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1126, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1125, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1130 | h1130
                  · linarith only [h1117, h1118, h1130, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1132 | h1132
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1133 | h1133
                      · linarith only [h0, h1133, h848, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1133, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1132, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1137 | h1137
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1138 | h1138
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1139 | h1139
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1140 | h1140
                      · linarith only [h0, h1140, h848, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1140, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1139, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1117, h1137, h1138, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1145 | h1145
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1146 | h1146
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1147 | h1147
                      · linarith only [h1145, h1147, h848, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                      · linarith only [h0, h1147, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1146, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1151 | h1151
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1152 | h1152
                      · linarith only [h0, h1152, h848, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1152, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1151, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
