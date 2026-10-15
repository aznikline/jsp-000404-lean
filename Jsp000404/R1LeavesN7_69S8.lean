import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_LI_L_0_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h10, h14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h14, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                          · linarith only [h0, h11, h12, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                        · linarith only [h0, h10, h20, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                          · linarith only [h0, h10, h22, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                                    · linarith only [h1, h24, h28, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h28, h9, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h27, h9, hc24, hlam, hphi, u4elo0]
                                · linarith only [h10, h26, h8, hc13, hlam, hphi, u3elo0]
                              · linarith only [h10, h25, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h24, h7, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                              · linarith only [h0, h35, h39, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h38, h39, hc23, hlam, hphi, u3elo1]
                            · linarith only [h38, h7, h9, hc13, hlam, hphi, ht34, u4elo4]
                          · linarith only [h0, h35, h37, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h35, h36, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                        · linarith only [h0, h35, h4, h45, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h45, h5, h9, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h48 | h48
                    · linarith only [h48, h7, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                              · linarith only [h0, h50, h54, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h1, h53, h54, h8, hc23, hlam, hphi, u3elo4]
                            · linarith only [h53, h7, h8, hc13, hlam, hphi, u3elo4]
                          · linarith only [h0, h51, h52, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h50, h51, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h4, h50, h8, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h61 | h61
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h62 | h62
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
                            · linarith only [h1, h66, h7, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                              · linarith only [h61, h63, h68, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                                · linarith only [h0, h64, h68, h70, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h61, h7, h70, hc23, hlam, hphi, u3elo3]
                          · linarith only [h0, h6, h64, h65, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h63, h64, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h4, h63, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h61, h62, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                            · linarith only [h1, h7, h81, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                              · linarith only [h7, h83, hc03, hlam, hphi, u3elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h1, h61, h78, h85, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                                  · linarith only [h0, h79, h87, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h77, h87, hc24, hlam, hphi, u4elo0]
                          · linarith only [h0, h6, h78, h80, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h78, h79, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h4, h7, h78, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                            · linarith only [h1, h7, h96, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                              · linarith only [h1, h7, h77, h93, h98, hc34, hlam, hphi, u4elo4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                                · linarith only [h0, h100, h94, h98, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h102 | h102
                                  · linarith only [h0, h102, h7, h77, h94, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h104 | h104
                                    · linarith only [h1, h104, h7, h77, h93, hc23, hlam, hphi, ht34, u4elo3]
                                    · linarith only [h1, h104, h7, h93, hc23, hlam, hphi, ht34, u4elo4]
                          · linarith only [h0, h6, h93, h95, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h93, h94, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h4, h7, h93, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
                · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
                  · linarith only [h111, h4, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
                    · linarith only [h113, h5, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
                          · linarith only [h0, h117, h6, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                              · linarith only [h0, h115, h120, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h110, h111, h120, hc23, hlam, hphi, u3elo4]
                            · linarith only [h110, h111, h119, hc13, hlam, hphi, u3elo4]
                        · linarith only [h116, h5, h6, hc12, hc25, hlam, hphi]
                      · linarith only [h113, h115, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h126 | h126
                  · linarith only [h110, h126, h4, h6, hc23, hlam, hphi, ht34, u4elo3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
                    · linarith only [h128, h5, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h131 | h131
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                          · linarith only [h0, h132, h6, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                            · linarith only [h1, h110, h128, h134, hc34, hlam, hphi, u4elo4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                              · linarith only [h0, h110, h130, h136, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                                · linarith only [h1, h126, h130, h138, hlam]
                                · linarith only [h0, h131, h136, h138, h6, hc23, hlam, hphi, u3elo4]
                        · linarith only [h131, h5, h6, hc12, hc25, hlam, hphi]
                      · linarith only [h128, h130, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h144 | h144
            · rcases m.htr 0 2 5 (by decide) (by decide) with h145 | h145
              · rcases m.htr 0 3 4 (by decide) (by decide) with h146 | h146
                · rcases m.htr 0 3 5 (by decide) (by decide) with h147 | h147
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h148 | h148
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h149 | h149
                      · linarith only [h144, h149, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h153 | h153
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                                  · linarith only [h0, h151, h156, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                  · linarith only [h144, h148, h154, h156, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h155, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h154, h4, hc02, hlam, hphi, ht23, u3elo3]
                            · linarith only [h144, h146, h153, h4, hc13, hlam, hphi, u3elo2]
                          · linarith only [h145, h151, h152, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h144, h151, h4, hc12, hlam, hphi, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
                      · linarith only [h144, h164, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h171 | h171
                                  · linarith only [h0, h148, h166, h171, h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
                                    · linarith only [h148, h166, h169, h173, h2, hlam]
                                    · rcases h0bigk with h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h0, h167, h171, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p175_1, u1elo0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h1, h164, h167, h169, h171, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p175_1, u1elo0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        rcases p175_3 (m.d 0 1) (by simp) with h179 | h179
                                        · rcases p175_3 (m.d 0 2) (by simp) with h180 | h180
                                          · linarith only [h0, h180, hlam]
                                          · linarith only [h144, h180, hlam]
                                        · linarith only [h179, h2, hlam]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        rcases p175_3 (m.d 0 1) (by simp) with h184 | h184
                                        · rcases p175_3 (m.d 0 2) (by simp) with h185 | h185
                                          · linarith only [h0, h185, hlam]
                                          · linarith only [h145, h185, hlam]
                                        · linarith only [h184, h3, hlam]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h0, hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h4, hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h166, h169, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p175_1, u3elo2]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p175_1, u3elo2]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h1, hlam, p175_1]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [hc02, hlam, hphi, ht23, p175_1, u3elo0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        rcases p175_3 (m.d 0 1) (by simp) with h197 | h197
                                        · rcases p175_3 (m.d 0 2) (by simp) with h198 | h198
                                          · linarith only [h198, h4, hlam]
                                          · linarith only [h144, h198, hlam]
                                        · linarith only [h197, h2, hlam]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        rcases p175_3 (m.d 0 1) (by simp) with h202 | h202
                                        · rcases p175_3 (m.d 0 2) (by simp) with h203 | h203
                                          · linarith only [h203, h4, hlam]
                                          · linarith only [h145, h203, hlam]
                                        · linarith only [h202, h3, hlam]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h2, hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h144, hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h146, hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h148, hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h3, hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h145, hlam, p175_1]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h147, hlam, p175_0]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [h145, h166, h169, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p175_1, u3elo2]
                                      · have p175_0 := h175c.1
                                        have p175_1 := h175c.2.1
                                        have p175_2 := h175c.2.2.1
                                        have p175_3 := h175c.2.2.2
                                        linarith only [hlam, p175_0]
                                · linarith only [h170, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h166, h169, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h146, h148, h164, h166, h168, hc24, hlam, hphi, u4elo4]
                          · linarith only [h145, h166, h167, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h144, h166, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h145, h147, h4, hlam]
                · linarith only [h144, h146, h4, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h224 | h224
                · rcases m.htr 0 3 5 (by decide) (by decide) with h225 | h225
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h226 | h226
                    · linarith only [h144, h145, h226, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h228 | h228
                      · linarith only [h0, h228, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h231 | h231
                          · linarith only [h0, h145, h231, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h233 | h233
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h236 | h236
                                  · linarith only [h0, h145, h226, h230, h235, h236, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · linarith only [h0, h145, h230, h236, hc24, hlam, hphi, u4elo4]
                                · linarith only [h0, h225, h230, h234, h235, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · linarith only [h1, h228, h230, h234, h4, hc24, hlam, hphi, u4elo3]
                            · linarith only [h224, h228, h230, h233, hc24, hlam, hphi, u4elo0]
                        · linarith only [h144, h230, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h243 | h243
                    · linarith only [h144, h225, h243, h4, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h245 | h245
                      · linarith only [h0, h225, h245, h4, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h247 | h247
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h248 | h248
                          · linarith only [h0, h145, h248, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h252 | h252
                                · linarith only [h0, h225, h247, h251, h252, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h0, h247, h251, h252, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · linarith only [h0, h247, h251, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h224, h250, hc13, hlam, hphi, u3elo0]
                        · linarith only [h144, h225, h247, h4, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h144, h224, h4, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h259 | h259
              · rcases m.htr 0 3 4 (by decide) (by decide) with h260 | h260
                · rcases m.htr 0 3 5 (by decide) (by decide) with h261 | h261
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h262 | h262
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h263 | h263
                      · linarith only [h0, h260, h263, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h265 | h265
                        · linarith only [h144, h259, h265, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h268 | h268
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h270 | h270
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h271 | h271
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h272 | h272
                                    · linarith only [h1, h268, h272, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h262, h272, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h144, h259, h262, h271, hlam]
                                · linarith only [h0, h144, h267, h269, h270, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                              · linarith only [h0, h267, h269, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                            · linarith only [h260, h268, hc13, hlam, hphi, u3elo0]
                          · linarith only [h144, h259, h267, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h144, h259, h262, hlam]
                  · linarith only [h259, h261, h4, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h283 | h283
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h284 | h284
                      · linarith only [h0, h144, h284, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h286 | h286
                        · linarith only [h144, h284, h286, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
                            · linarith only [h1, h260, h289, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                              · linarith only [h0, h260, h288, h291, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h0, h288, h291, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h144, h259, h288, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h259, h260, h283, h4, hlam]
                  · linarith only [h259, h282, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h297 | h297
                · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
                      · linarith only [h0, h300, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
                        · linarith only [h0, h144, h302, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                          · linarith only [h0, h259, h304, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h307 | h307
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h308 | h308
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h309 | h309
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                                    · linarith only [h1, h306, h310, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h299, h310, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h299, h309, hc24, hlam, hphi, u4elo0]
                                · linarith only [h0, h144, h298, h307, h308, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h306, h307, h4, hc03, hlam, hphi, u3elo1]
                            · linarith only [h297, h306, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
                      · linarith only [h0, h144, h317, h4, hc03, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                        · linarith only [h0, h144, h319, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
                          · linarith only [h0, h259, h321, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h323 | h323
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h324 | h324
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h325 | h325
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h326 | h326
                                  · linarith only [h144, h299, h324, h326, hc02, hlam, hphi, ht23, u3elo2]
                                  · linarith only [h0, h144, h326, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h298, h325, hc23, hlam, hphi, u3elo0]
                              · linarith only [h323, h324, h4, hc03, hlam, hphi, u3elo1]
                            · linarith only [h297, h323, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
                    · linarith only [h297, h298, h332, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
                      · linarith only [h0, h144, h334, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h336 | h336
                        · linarith only [h0, h144, h332, h336, hc24, hlam, hphi, u4elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h338 | h338
                          · linarith only [h0, h259, h338, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h342 | h342
                                · linarith only [h1, h298, h340, h342, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h342, h4, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h1, h340, h341, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h297, h298, h340, hc13, hlam, hphi, u3elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h347 | h347
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
                      · linarith only [h0, h349, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h351 | h351
                        · linarith only [h144, h349, h351, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
                          · linarith only [h0, h259, h353, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                            · linarith only [h1, h297, h355, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                              · linarith only [h297, h357, hc03, hlam, hphi, u3elo2]
                              · linarith only [h0, h357, h4, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h297, h347, h348, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h361 | h361
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
                      · linarith only [h0, h362, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h364 | h364
                        · linarith only [h0, h144, h364, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h366 | h366
                          · linarith only [h0, h259, h366, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                            · linarith only [h1, h297, h368, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
                              · linarith only [h297, h370, h4, hc02, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h370, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                      · linarith only [h0, h373, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h375 | h375
                        · linarith only [h0, h144, h375, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                          · linarith only [h0, h259, h377, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h379 | h379
                            · linarith only [h1, h297, h379, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h381 | h381
                              · linarith only [h297, h381, h4, hc02, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h381, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h384 | h384
          · rcases m.htr 0 2 4 (by decide) (by decide) with h385 | h385
            · rcases m.htr 0 2 5 (by decide) (by decide) with h386 | h386
              · linarith only [h0, h3, h386, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h388 | h388
                · rcases m.htr 0 3 5 (by decide) (by decide) with h389 | h389
                  · linarith only [h1, h3, h389, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h391 | h391
                    · linarith only [h2, h3, h391, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h393 | h393
                      · linarith only [h0, h3, h393, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                      · linarith only [h0, h3, h384, h393, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h396 | h396
                  · linarith only [h1, h3, h396, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h398 | h398
                    · linarith only [h0, h3, h385, h398, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
                      · linarith only [h0, h3, h400, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                      · linarith only [h0, h3, h384, h400, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · linarith only [h384, h385, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h404 | h404
            · rcases m.htr 0 2 5 (by decide) (by decide) with h405 | h405
              · linarith only [h0, h3, h384, h405, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
                · rcases m.htr 0 3 5 (by decide) (by decide) with h408 | h408
                  · linarith only [h1, h3, h408, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h410 | h410
                    · linarith only [h2, h3, h410, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h412 | h412
                      · linarith only [h0, h384, h408, h412, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
                        · linarith only [h0, h3, h414, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h384, h404, h408, h414, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h384, h404, h407, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h418 | h418
              · linarith only [h1, h3, h404, h418, hc13, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h420 | h420
                · rcases m.htr 0 3 5 (by decide) (by decide) with h421 | h421
                  · linarith only [h1, h3, h421, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h423 | h423
                    · linarith only [h0, h3, h420, h421, h423, hc12, hlam, hphi, ht23, u3elo4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
                      · linarith only [h0, h384, h425, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h427 | h427
                        · linarith only [h0, h3, h427, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h429 | h429
                          · linarith only [h1, h3, h418, h425, h429, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h431 | h431
                            · linarith only [h1, h3, h431, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                            · linarith only [h420, h421, h425, h431, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h434 | h434
                  · linarith only [h1, h3, h420, h434, hc13, hlam, hphi, ht34, u4elo3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
                    · linarith only [h2, h3, h436, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h438 | h438
                      · linarith only [h0, h404, h438, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h440 | h440
                        · linarith only [h0, h3, h440, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h442 | h442
                          · linarith only [h1, h3, h438, h442, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                            · linarith only [h1, h3, h444, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                              · linarith only [h384, h420, h446, hc02, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h384, h446, hc12, hlam, hphi, ht23, u3elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h451 | h451
    · rcases m.htr 0 1 4 (by decide) (by decide) with h452 | h452
      · rcases m.htr 0 1 5 (by decide) (by decide) with h453 | h453
        · rcases m.htr 0 2 3 (by decide) (by decide) with h454 | h454
          · rcases m.htr 0 2 4 (by decide) (by decide) with h455 | h455
            · rcases m.htr 0 2 5 (by decide) (by decide) with h456 | h456
              · rcases m.htr 0 3 4 (by decide) (by decide) with h457 | h457
                · rcases m.htr 0 3 5 (by decide) (by decide) with h458 | h458
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h461 | h461
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h462 | h462
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
                            · linarith only [h0, h451, h463, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h457, h460, h463, hc23, hlam, hphi, u3elo0]
                          · linarith only [h0, h456, h462, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h451, h460, h461, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h0, h460, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h469 | h469
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h470 | h470
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h471 | h471
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
                            · linarith only [h0, h451, h472, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h0, h451, h457, h472, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h0, h456, h471, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h451, h469, h470, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h0, h451, h469, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
                    · linarith only [h457, h458, h478, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h480 | h480
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h482 | h482
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h483 | h483
                            · linarith only [h0, h451, h483, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h457, h458, h483, hc13, hlam, hphi, u3elo4]
                          · linarith only [h0, h456, h482, hlam]
                        · linarith only [h0, h481, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h480, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h490 | h490
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h493 | h493
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                            · linarith only [h451, h457, h494, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h496 | h496
                              · linarith only [h0, h452, h457, h489, h491, h494, h496, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h498 | h498
                                · linarith only [h0, h452, h491, h494, h498, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · linarith only [h457, h489, h498, hc23, hlam, hphi, u3elo3]
                          · linarith only [h0, h456, h493, hlam]
                        · linarith only [h0, h451, h491, h492, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h0, h491, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h457, h489, h490, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h505 | h505
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h506 | h506
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h507 | h507
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h508 | h508
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h509 | h509
                            · linarith only [h0, h451, h509, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h511 | h511
                              · linarith only [h0, h452, h457, h506, h509, h511, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h513 | h513
                                · linarith only [h0, h451, h506, h513, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h515 | h515
                                  · linarith only [h0, h452, h507, h515, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                  · linarith only [h0, h452, h505, h515, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h0, h456, h508, hlam]
                        · linarith only [h0, h507, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h451, h506, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h521 | h521
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h522 | h522
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h523 | h523
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h524 | h524
                            · linarith only [h451, h457, h524, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h526 | h526
                              · linarith only [h451, h457, h521, h526, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h528 | h528
                                · linarith only [h451, h489, h521, h528, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h530 | h530
                                  · linarith only [h0, h451, h452, h457, h505, h521, h522, h530, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h532 | h532
                                    · linarith only [h451, h457, h505, h521, h532, hc23, hlam, hphi, u3elo3]
                                    · linarith only [h451, h457, h521, h532, hc23, hlam, hphi, ht34, u4elo4]
                          · linarith only [h0, h456, h523, hlam]
                        · linarith only [h0, h522, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h451, h521, hc13, hlam, hphi, u3elo2]
              · linarith only [h0, h453, h456, hlam]
            · linarith only [h0, h451, h455, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h451, h454, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h541 | h541
          · rcases m.htr 0 2 4 (by decide) (by decide) with h542 | h542
            · rcases m.htr 0 2 5 (by decide) (by decide) with h543 | h543
              · rcases m.htr 0 3 4 (by decide) (by decide) with h544 | h544
                · rcases m.htr 0 3 5 (by decide) (by decide) with h545 | h545
                  · linarith only [h451, h453, h545, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h547 | h547
                    · linarith only [h451, h453, h544, h547, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h549 | h549
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h550 | h550
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h551 | h551
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h552 | h552
                            · linarith only [h451, h453, h551, h552, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h544, h545, h552, hc13, hlam, hphi, u3elo4]
                          · linarith only [h0, h452, h543, h550, h551, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h0, h451, h549, h550, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h0, h549, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h558 | h558
                  · linarith only [h451, h453, h544, h558, hc13, hlam, hphi, ht34, u4elo3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h560 | h560
                    · linarith only [h452, h453, h560, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h563 | h563
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h564 | h564
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h565 | h565
                            · linarith only [h451, h453, h564, h565, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h567 | h567
                              · linarith only [h544, h562, h567, hc03, hlam, hphi, u3elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
                                · linarith only [h451, h453, h558, h562, h564, h569, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h571 | h571
                                  · linarith only [h452, h453, h560, h563, h564, h571, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                                    · linarith only [h452, h453, h560, h565, h573, hc13, hlam, hphi, u3elo3]
                                    · linarith only [h544, h573, hc03, hlam, hphi, ht34, u4elo4]
                          · linarith only [h0, h543, h564, hlam]
                        · linarith only [h0, h452, h563, hc14, hlam, hphi, u4elo2]
                      · linarith only [h0, h451, h562, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h579 | h579
                · rcases m.htr 0 3 5 (by decide) (by decide) with h580 | h580
                  · linarith only [h0, h451, h543, h580, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h582 | h582
                    · linarith only [h0, h452, h543, h582, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h584 | h584
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h585 | h585
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h586 | h586
                          · linarith only [h0, h543, h586, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h588 | h588
                            · linarith only [h0, h451, h586, h588, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h579, h580, h588, hc13, hlam, hphi, u3elo4]
                        · linarith only [h0, h585, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h451, h584, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h593 | h593
                  · linarith only [h0, h451, h543, h593, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h595 | h595
                    · linarith only [h0, h452, h543, h595, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h597 | h597
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h598 | h598
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h599 | h599
                          · linarith only [h0, h451, h543, h597, h599, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h601 | h601
                            · linarith only [h0, h451, h599, h601, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h603 | h603
                              · linarith only [h579, h603, hc03, hlam, hphi, u3elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h605 | h605
                                · linarith only [h0, h452, h543, h593, h597, h601, h605, hlam]
                                · linarith only [h0, h452, h597, h599, h601, h605, hc23, hlam, hphi, u3elo4]
                        · linarith only [h0, h598, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h597, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h0, h451, h542, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h451, h541, hc13, hlam, hphi, u3elo2]
      · linarith only [h451, h452, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h613 | h613
      · rcases m.htr 0 1 5 (by decide) (by decide) with h614 | h614
        · rcases m.htr 0 2 3 (by decide) (by decide) with h615 | h615
          · rcases m.htr 0 2 4 (by decide) (by decide) with h616 | h616
            · rcases m.htr 0 2 5 (by decide) (by decide) with h617 | h617
              · rcases m.htr 0 3 4 (by decide) (by decide) with h618 | h618
                · rcases m.htr 0 3 5 (by decide) (by decide) with h619 | h619
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h622 | h622
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h623 | h623
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h624 | h624
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h625 | h625
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h626 | h626
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h627 | h627
                                  · linarith only [h451, h613, h622, h627, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                  · linarith only [h451, h613, h620, h625, h627, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h619, h625, h626, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · linarith only [h451, h618, h625, hc23, hlam, hphi, u3elo1]
                            · linarith only [h451, h613, h618, h624, hlam]
                          · linarith only [h451, h617, h621, h623, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h613, h622, hc14, hlam, hphi, u4elo2]
                      · linarith only [h0, h613, h621, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h636 | h636
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h637 | h637
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h638 | h638
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h639 | h639
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h640 | h640
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h641 | h641
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
                                  · linarith only [h613, h620, h637, h642, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h644 | h644
                                    · linarith only [h451, h614, h620, h638, h640, h642, h644, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                    · rcases h0bigk with h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h0, hlam, p646_1]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h451, hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h451, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p646_1, u3elo1]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h451, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p646_1, u3elo1]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p646_1, u1elo1]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h0, h451, h613, h637, h640, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p646_1, u1elo1]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        rcases p646_3 (m.d 0 1) (by simp) with h655 | h655
                                        · linarith only [h0, h655, hlam]
                                        · linarith only [h613, h655, hlam]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        rcases p646_3 (m.d 0 1) (by simp) with h658 | h658
                                        · linarith only [h0, h658, hlam]
                                        · linarith only [h614, h658, hlam]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h614, h638, h640, h642, hc34, hlam, hphi, ht0b, ht45, ht5b, p646_1, u0elo2]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h615, hlam, p646_1]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        rcases p646_3 (m.d 0 1) (by simp) with h664 | h664
                                        · linarith only [h451, h664, hlam]
                                        · linarith only [h613, h664, hlam]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        rcases p646_3 (m.d 0 1) (by simp) with h667 | h667
                                        · linarith only [h451, h667, hlam]
                                        · linarith only [h614, h667, hlam]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h613, hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h616, hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h618, hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h620, hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h614, hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h617, hlam, p646_1]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h619, hlam, p646_0]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [h0, h613, h614, h637, h640, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p646_1, u1elo1]
                                      · have p646_0 := h646c.1
                                        have p646_1 := h646c.2.1
                                        have p646_2 := h646c.2.2.1
                                        have p646_3 := h646c.2.2.2
                                        linarith only [hlam, p646_0]
                                · linarith only [h451, h619, h641, hc23, hlam, hphi, u3elo1]
                              · linarith only [h451, h618, h640, hc23, hlam, hphi, u3elo1]
                            · linarith only [h451, h613, h618, h637, h639, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h0, h617, h638, hlam]
                        · linarith only [h0, h637, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h613, h636, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h451, h614, h619, hlam]
                · linarith only [h451, h613, h618, hc14, hlam, hphi, u4elo3]
              · linarith only [h0, h614, h617, hlam]
            · linarith only [h451, h613, h615, h616, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h690 | h690
            · rcases m.htr 0 2 5 (by decide) (by decide) with h691 | h691
              · rcases m.htr 0 3 4 (by decide) (by decide) with h692 | h692
                · rcases m.htr 0 3 5 (by decide) (by decide) with h693 | h693
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h694 | h694
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h695 | h695
                      · linarith only [h0, h613, h615, h695, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h613, h695, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h698 | h698
                      · linarith only [h0, h613, h615, h698, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h613, h698, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h0, h614, h615, h693, hlam]
                · linarith only [h0, h613, h615, h692, hc14, hlam, hphi, u4elo3]
              · linarith only [h0, h614, h691, hlam]
            · linarith only [h0, h613, h690, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h705 | h705
          · rcases m.htr 0 2 4 (by decide) (by decide) with h706 | h706
            · rcases m.htr 0 2 5 (by decide) (by decide) with h707 | h707
              · rcases m.htr 0 3 4 (by decide) (by decide) with h708 | h708
                · rcases m.htr 0 3 5 (by decide) (by decide) with h709 | h709
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h710 | h710
                    · linarith only [h613, h614, h710, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h712 | h712
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h713 | h713
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h714 | h714
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h715 | h715
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h716 | h716
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h717 | h717
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h718 | h718
                                  · linarith only [h613, h710, h713, h718, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h720 | h720
                                    · linarith only [h613, h614, h710, h713, h716, h720, hlam]
                                    · rcases h0bigk with h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h0, hlam, p722_1]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h451, hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h451, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p722_1, u3elo1]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h614, hlam, p722_1]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p722_1, u1elo1]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h0, h451, h613, h713, h716, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p722_1, u1elo1]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        rcases p722_3 (m.d 0 1) (by simp) with h731 | h731
                                        · linarith only [h0, h731, hlam]
                                        · linarith only [h613, h731, hlam]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h0, h613, h614, h713, h716, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p722_1, u1elo1]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h613, h713, h716, hc34, hlam, hphi, ht0b, ht45, ht5b, p722_1, u0elo2]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h705, hlam, p722_1]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        rcases p722_3 (m.d 0 1) (by simp) with h738 | h738
                                        · linarith only [h451, h738, hlam]
                                        · linarith only [h613, h738, hlam]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h451, h613, h614, h713, h716, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p722_1, u3elo1]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h613, hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h706, hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h708, hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h710, hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h613, h713, h716, hc34, hlam, hphi, ht0b, ht45, ht5b, p722_1, u0elo4]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h707, hlam, p722_1]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h709, hlam, p722_0]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [h613, h710, h713, h716, hc34, hlam, hphi, p722_1, u4elo4]
                                      · have p722_0 := h722c.1
                                        have p722_1 := h722c.2.1
                                        have p722_2 := h722c.2.2.1
                                        have p722_3 := h722c.2.2.2
                                        linarith only [hlam, p722_0]
                                · linarith only [h451, h709, h717, hc23, hlam, hphi, u3elo1]
                              · linarith only [h451, h708, h716, hc23, hlam, hphi, u3elo1]
                            · linarith only [h451, h715, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h0, h707, h714, hlam]
                        · linarith only [h0, h713, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h613, h712, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h758 | h758
                    · linarith only [h613, h614, h758, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h761 | h761
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h762 | h762
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h763 | h763
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h764 | h764
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h765 | h765
                                · linarith only [h705, h709, h765, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h767 | h767
                                  · linarith only [h451, h613, h709, h758, h761, h767, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h769 | h769
                                    · linarith only [h451, h613, h709, h758, h761, h764, h769, hlam]
                                    · linarith only [h451, h613, h709, h769, hc14, hlam, hphi, u4elo4]
                              · linarith only [h708, h709, h764, hc23, hlam, hphi, u3elo4]
                            · linarith only [h451, h613, h708, h761, h763, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h0, h613, h707, h761, h762, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h451, h760, h761, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h613, h760, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h451, h613, h708, hc14, hlam, hphi, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h778 | h778
                · rcases m.htr 0 3 5 (by decide) (by decide) with h779 | h779
                  · linarith only [h705, h707, h779, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
                    · linarith only [h451, h613, h705, h707, h781, hc23, hlam, hphi, u3elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h785 | h785
                          · linarith only [h451, h613, h705, h707, h784, h785, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h787 | h787
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h788 | h788
                              · linarith only [h705, h707, h781, h788, hc34, hlam, hphi, u4elo4]
                              · linarith only [h778, h779, h788, hc23, hlam, hphi, u3elo4]
                            · linarith only [h778, h779, h787, hc13, hlam, hphi, u3elo4]
                        · linarith only [h0, h613, h784, hc14, hlam, hphi, u4elo2]
                      · linarith only [h0, h613, h783, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h451, h613, h778, hc14, hlam, hphi, u4elo3]
            · linarith only [h0, h613, h706, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h796 | h796
            · rcases m.htr 0 2 5 (by decide) (by decide) with h797 | h797
              · rcases m.htr 0 3 4 (by decide) (by decide) with h798 | h798
                · rcases m.htr 0 3 5 (by decide) (by decide) with h799 | h799
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h800 | h800
                    · linarith only [h613, h614, h800, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                      · linarith only [h613, h614, h705, h797, h802, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h613, h802, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h705, h797, h799, hlam]
                · linarith only [h613, h614, h705, h797, h798, hc14, hlam, hphi, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h807 | h807
                · rcases m.htr 0 3 5 (by decide) (by decide) with h808 | h808
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h809 | h809
                    · linarith only [h0, h613, h797, h809, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h811 | h811
                      · linarith only [h0, h613, h705, h811, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h613, h811, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h814 | h814
                    · linarith only [h451, h613, h808, h814, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h816 | h816
                      · linarith only [h0, h613, h705, h816, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h613, h816, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h0, h613, h705, h807, hc14, hlam, hphi, u4elo3]
            · linarith only [h0, h613, h796, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h821 | h821
        · rcases m.htr 0 2 3 (by decide) (by decide) with h822 | h822
          · rcases m.htr 0 2 4 (by decide) (by decide) with h823 | h823
            · rcases m.htr 0 2 5 (by decide) (by decide) with h824 | h824
              · rcases m.htr 0 3 4 (by decide) (by decide) with h825 | h825
                · rcases m.htr 0 3 5 (by decide) (by decide) with h826 | h826
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h827 | h827
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h828 | h828
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h829 | h829
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h830 | h830
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h831 | h831
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h832 | h832
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h833 | h833
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h834 | h834
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h835 | h835
                                    · linarith only [h822, h832, h835, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h827, h835, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h613, h821, h827, h834, hc24, hlam, hphi, u4elo1]
                                · linarith only [h826, h833, hc23, hlam, hphi, u3elo0]
                              · linarith only [h451, h825, h832, hc23, hlam, hphi, u3elo1]
                            · linarith only [h451, h825, h831, hlam]
                          · linarith only [h0, h824, h830, hlam]
                        · linarith only [h0, h829, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h821, h828, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h613, h821, h827, hlam]
                  · linarith only [h613, h821, h825, h826, hc34, hlam, hphi, u4elo1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h847 | h847
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h848 | h848
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h849 | h849
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h850 | h850
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h851 | h851
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h852 | h852
                            · linarith only [h451, h821, h825, h851, h852, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h451, h821, h851, h852, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h0, h824, h851, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h821, h850, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                      · linarith only [h0, h821, h822, h849, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h451, h821, h825, h848, hlam]
                  · linarith only [h451, h821, h847, hlam]
              · linarith only [h0, h821, h824, hlam]
            · linarith only [h822, h823, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h862 | h862
            · rcases m.htr 0 2 5 (by decide) (by decide) with h863 | h863
              · rcases m.htr 0 3 4 (by decide) (by decide) with h864 | h864
                · rcases m.htr 0 3 5 (by decide) (by decide) with h865 | h865
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h866 | h866
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h867 | h867
                      · linarith only [h613, h821, h822, h862, h867, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h0, h821, h867, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h613, h821, h866, hlam]
                  · linarith only [h613, h821, h822, h862, h865, hlam]
                · linarith only [h822, h862, h864, hc24, hlam, hphi, u4elo3]
              · linarith only [h613, h821, h862, h863, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h874 | h874
              · rcases m.htr 0 3 4 (by decide) (by decide) with h875 | h875
                · rcases m.htr 0 3 5 (by decide) (by decide) with h876 | h876
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h877 | h877
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                      · linarith only [h822, h874, h878, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h0, h821, h878, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h0, h821, h862, h877, hlam]
                  · linarith only [h0, h821, h862, h875, h876, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h883 | h883
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h884 | h884
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h885 | h885
                      · linarith only [h0, h821, h822, h885, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h0, h821, h885, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h451, h821, h875, h884, hlam]
                  · linarith only [h0, h821, h822, h883, hlam]
              · linarith only [h0, h821, h874, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h891 | h891
          · rcases m.htr 0 2 4 (by decide) (by decide) with h892 | h892
            · rcases m.htr 0 2 5 (by decide) (by decide) with h893 | h893
              · rcases m.htr 0 3 4 (by decide) (by decide) with h894 | h894
                · rcases m.htr 0 3 5 (by decide) (by decide) with h895 | h895
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h896 | h896
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h897 | h897
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h898 | h898
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h899 | h899
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h900 | h900
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h901 | h901
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h902 | h902
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h903 | h903
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h904 | h904
                                    · linarith only [h891, h901, h904, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h896, h904, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h613, h896, h903, hc24, hlam, hphi, u4elo1]
                                · linarith only [h895, h902, hc23, hlam, hphi, u3elo0]
                              · linarith only [h451, h894, h901, hc23, hlam, hphi, u3elo1]
                            · linarith only [h451, h894, h900, hlam]
                          · linarith only [h0, h893, h899, hlam]
                        · linarith only [h0, h898, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h897, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h914 | h914
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h915 | h915
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h916 | h916
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h917 | h917
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h918 | h918
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h919 | h919
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h920 | h920
                                  · linarith only [h896, h920, hc04, hlam, hphi, u4elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h922 | h922
                                    · linarith only [h613, h891, h896, h918, h922, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                    · rcases h0bigk with h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [hlam, p924_0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h0, hlam, p924_1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h451, hlam, p924_0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h613, hlam, p924_1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h821, hlam, p924_1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p924_1, u1elo1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [hlam, p924_0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h0, h451, hc01, hlam, hphi, p924_1, u1elo1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h0, h613, hc01, hlam, hphi, p924_1, u1elo1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h0, h821, hc01, hlam, hphi, p924_1, u1elo1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p924_1, u3elo0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h891, hlam, p924_1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [hlam, p924_0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h451, h613, hc01, hlam, hphi, ht12, ht23, p924_1, u3elo1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h451, h821, hc01, hlam, hphi, ht12, ht23, p924_1, u3elo1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p924_1, u4elo0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h892, hlam, p924_0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h894, hlam, p924_0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [hlam, p924_0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h896, hlam, p924_0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h896, hc01, hlam, hphi, ht12, ht23, ht34, p924_1, u4elo4]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h893, hlam, p924_1]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h895, hlam, p924_0]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [h896, hc04, hlam, hphi, p924_1, u4elo4]
                                      · have p924_0 := h924c.1
                                        have p924_1 := h924c.2.1
                                        have p924_2 := h924c.2.2.1
                                        have p924_3 := h924c.2.2.2
                                        linarith only [hlam, p924_0]
                                · linarith only [h451, h895, h919, hc23, hlam, hphi, u3elo1]
                              · linarith only [h451, h894, h918, hc23, hlam, hphi, u3elo1]
                            · linarith only [h451, h917, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h0, h893, h916, hlam]
                        · linarith only [h0, h915, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h914, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h956 | h956
                    · linarith only [h894, h895, h956, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h958 | h958
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h959 | h959
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h960 | h960
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h961 | h961
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h962 | h962
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h963 | h963
                                · linarith only [h891, h895, h963, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h965 | h965
                                  · linarith only [h892, h956, h965, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h967 | h967
                                    · linarith only [h891, h895, h956, h962, h967, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                    · linarith only [h891, h895, h962, h967, hc34, hlam, hphi, u4elo4]
                              · linarith only [h894, h895, h962, hc23, hlam, hphi, u3elo4]
                            · linarith only [h894, h895, h961, hc13, hlam, hphi, u3elo4]
                          · linarith only [h0, h893, h960, hlam]
                        · linarith only [h0, h959, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h891, h958, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h975 | h975
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h976 | h976
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h977 | h977
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h978 | h978
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h979 | h979
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h980 | h980
                            · linarith only [h894, h975, h980, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h451, h980, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h0, h893, h975, h979, hc01, hlam, hphi, ht12, ht23, u3elo0]
                        · linarith only [h451, h892, h977, h978, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h977, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h894, h975, h976, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h987 | h987
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h988 | h988
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h989 | h989
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h990 | h990
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h991 | h991
                            · linarith only [h894, h991, hc03, hlam, hphi, u3elo1]
                            · linarith only [h451, h991, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h451, h893, h988, h990, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h892, h989, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                      · linarith only [h0, h891, h988, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h997 | h997
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h998 | h998
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h999 | h999
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1000 | h1000
                            · linarith only [h1000, h451, h894, hc01, hlam, hphi, u1elo2]
                            · linarith only [h1000, h451, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h0, h821, h893, h999, hc01, hlam, hphi, u1elo4]
                        · linarith only [h0, h892, h998, hlam]
                      · linarith only [h0, h891, h997, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1006 | h1006
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1007 | h1007
                  · linarith only [h1007, h891, h893, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1009 | h1009
                    · linarith only [h1009, h892, h893, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1011 | h1011
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1012 | h1012
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1013 | h1013
                          · linarith only [h1013, h891, h893, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1015 | h1015
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1016 | h1016
                              · linarith only [h1009, h1016, h891, h893, hc34, hlam, hphi, u4elo4]
                              · linarith only [h1006, h1007, h1016, hc23, hlam, hphi, u3elo4]
                            · linarith only [h1006, h1007, h1015, hc13, hlam, hphi, u3elo4]
                        · linarith only [h1009, h1012, h892, h893, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h0, h1011, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1022 | h1022
                  · linarith only [h1022, h891, h893, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1024 | h1024
                    · linarith only [h1024, h892, h893, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1026 | h1026
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1027 | h1027
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1028 | h1028
                          · linarith only [h1028, h891, h893, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1030 | h1030
                            · linarith only [h1006, h1030, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1030, h451, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h1026, h1027, h451, h892, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1026, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h891, h892, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1036 | h1036
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1037 | h1037
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1038 | h1038
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1039 | h1039
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1040 | h1040
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1041 | h1041
                      · linarith only [h1036, h1041, h891, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h1041, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1044 | h1044
                      · linarith only [h1036, h1044, h891, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h1044, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1037, h1039, h891, hlam]
                · linarith only [h1036, h1038, h891, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1049 | h1049
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1050 | h1050
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1051 | h1051
                    · linarith only [h1036, h1037, h1051, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1053 | h1053
                      · linarith only [h1036, h1053, h891, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h1053, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1056 | h1056
                    · linarith only [h1036, h1050, h1056, h891, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1058 | h1058
                      · linarith only [h1036, h1058, h891, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h1058, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1036, h1049, h891, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1062 | h1062
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1063 | h1063
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1064 | h1064
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1065 | h1065
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1066 | h1066
                      · linarith only [h1062, h1066, h891, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h0, h1066, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h1036, h1062, h1065, hlam]
                  · linarith only [h1062, h1064, h891, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1071 | h1071
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1072 | h1072
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1073 | h1073
                      · linarith only [h0, h1073, h891, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1073, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h1062, h1063, h1072, h891, hlam]
                  · linarith only [h1062, h1071, h891, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1078 | h1078
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1079 | h1079
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1080 | h1080
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1081 | h1081
                      · linarith only [h0, h1081, h891, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1081, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1084 | h1084
                      · linarith only [h0, h1084, h891, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1084, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1087 | h1087
                    · linarith only [h1078, h1079, h1087, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1089 | h1089
                      · linarith only [h0, h1089, h891, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1089, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1092 | h1092
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1093 | h1093
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1094 | h1094
                      · linarith only [h0, h1094, h891, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1094, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h1078, h1092, h1093, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1098 | h1098
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1099 | h1099
                      · linarith only [h0, h1099, h891, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1099, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1102 | h1102
                      · linarith only [h0, h1102, h891, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1102, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h2, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11 | h11
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
              · linarith only [h0, h12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h12, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
              · linarith only [h0, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h15, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · linarith only [h2, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h19 | h19
        · rcases m.htr 0 3 4 (by decide) (by decide) with h20 | h20
          · linarith only [h2, h20, h3, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
              · linarith only [h0, h23, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h2, h23, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
              · linarith only [h0, h26, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h2, h26, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
        · linarith only [h19, h2, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
      · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
        · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
          · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
            · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
              · linarith only [h0, h2, h30, h34, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                · linarith only [h0, h36, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h30, h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2, h30, h33, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h2, h30, h32, hlam]
        · linarith only [h30, h31, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h42 | h42
        · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
          · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
            · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
              · linarith only [h0, h2, h45, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                · linarith only [h0, h30, h42, h47, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                  · linarith only [h1, h45, h49, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h42, h49, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h30, h42, h43, h44, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h53 | h53
            · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
              · linarith only [h0, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
                · linarith only [h1, h30, h42, h54, h56, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
                  · linarith only [h1, h54, h58, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h42, h58, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2, h42, h53, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h62 | h62
          · rcases m.htr 0 3 5 (by decide) (by decide) with h63 | h63
            · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
              · linarith only [h0, h64, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
                · linarith only [h0, h30, h66, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
                  · linarith only [h0, h42, h68, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h70 | h70
                    · linarith only [h1, h70, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h62, h70, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · linarith only [h62, h63, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h74 | h74
            · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
              · linarith only [h0, h2, h75, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                · linarith only [h0, h30, h77, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                  · linarith only [h0, h42, h79, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                    · linarith only [h1, h62, h74, h81, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                      · linarith only [h1, h83, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h74, h83, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
              · linarith only [h0, h2, h86, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                · linarith only [h0, h30, h88, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                  · linarith only [h0, h2, h74, h90, hc25, hlam, hphi, u5elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                    · linarith only [h1, h2, h62, h92, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                      · linarith only [h1, h94, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                              · rcases h2bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h2, h74, h97, hc12, hlam, hphi, ht23, ht34, ht45, p100_1, u5elo2]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h2, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h30, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h42, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h0, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h86, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h88, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h90, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  rcases p100_3 (m.d 0 2) (by simp) with h111 | h111
                                  · linarith only [h111, hlam, p100_0]
                                  · rcases p100_3 (m.d 1 2) (by simp) with h113 | h113
                                    · linarith only [h113, h86, hlam]
                                    · rcases p100_3 (m.d 2 3) (by simp) with h115 | h115
                                      · rcases p100_3 (m.d 2 4) (by simp) with h116 | h116
                                        · linarith only [h116, h96, hlam]
                                        · linarith only [h116, h30, hlam]
                                      · linarith only [h115, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  rcases p100_3 (m.d 0 2) (by simp) with h120 | h120
                                  · linarith only [h120, h2, hlam]
                                  · linarith only [h0, h120, hlam]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h2, h74, h97, h98, hc02, hc23, hlam, hphi, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h0, h2, h74, h97, hc12, hc23, hlam, hphi, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  rcases p100_3 (m.d 0 2) (by simp) with h126 | h126
                                  · linarith only [h126, hlam, p100_0]
                                  · rcases p100_3 (m.d 1 2) (by simp) with h128 | h128
                                    · linarith only [h128, h88, hlam]
                                    · rcases p100_3 (m.d 2 3) (by simp) with h130 | h130
                                      · rcases p100_3 (m.d 2 4) (by simp) with h131 | h131
                                        · rcases p100_3 (m.d 2 5) (by simp) with h132 | h132
                                          · linarith only [h132, h98, hlam]
                                          · linarith only [h132, h42, hlam]
                                        · linarith only [h131, hlam, p100_0]
                                      · linarith only [h130, h2, hlam]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  rcases p100_3 (m.d 0 2) (by simp) with h137 | h137
                                  · linarith only [h137, h30, hlam]
                                  · linarith only [h0, h137, hlam]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h96, hlam, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h0, h2, h74, h97, hc12, hc24, hlam, hphi, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p100_1, u5elo2]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p100_1, u5elo2]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h97, hlam, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h98, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                              · linarith only [h0, h2, h62, h99, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h0, h30, h98, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h2, h97, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h151 | h151
                          · linarith only [h0, h151, h2, h74, h96, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h151, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h154 | h154
    · linarith only [h0, h1, h154, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h156 | h156
      · rcases m.htr 0 2 5 (by decide) (by decide) with h157 | h157
        · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
          · rcases m.htr 0 3 5 (by decide) (by decide) with h159 | h159
            · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
              · linarith only [h0, h154, h156, h160, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                · linarith only [h0, h1, h162, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h156, h162, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1, h157, h159, hc25, hlam, hphi, u5elo3]
          · linarith only [h0, h1, h156, h158, hlam]
        · linarith only [h156, h157, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h168 | h168
        · rcases m.htr 0 3 4 (by decide) (by decide) with h169 | h169
          · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
            · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
              · linarith only [h0, h154, h168, h171, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
                · linarith only [h0, h1, h156, h168, h173, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                  · linarith only [h0, h1, h175, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h168, h175, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1, h168, h170, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
            · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
              · linarith only [h0, h1, h154, h168, h169, h180, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h182 | h182
                · linarith only [h0, h1, h156, h168, h169, h182, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h184 | h184
                  · linarith only [h0, h1, h169, h184, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h168, h184, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1, h168, h179, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h188 | h188
          · rcases m.htr 0 3 5 (by decide) (by decide) with h189 | h189
            · rcases m.htr 1 2 3 (by decide) (by decide) with h190 | h190
              · linarith only [h0, h154, h190, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                · linarith only [h0, h168, h192, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                  · linarith only [h0, h1, h168, h194, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                              · linarith only [h188, h201, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                              · rcases h2bigk with h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p203_1, u0elo1]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h154, hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h156, hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h168, hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h0, hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h190, hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h192, hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h194, hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  rcases p203_3 (m.d 0 2) (by simp) with h214 | h214
                                  · linarith only [h214, hlam, p203_0]
                                  · rcases p203_3 (m.d 1 2) (by simp) with h216 | h216
                                    · linarith only [h190, h216, hlam]
                                    · rcases p203_3 (m.d 2 3) (by simp) with h218 | h218
                                      · rcases p203_3 (m.d 2 4) (by simp) with h219 | h219
                                        · linarith only [h198, h219, hlam]
                                        · linarith only [h156, h219, hlam]
                                      · linarith only [h218, hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  rcases p203_3 (m.d 0 2) (by simp) with h223 | h223
                                  · linarith only [h154, h223, hlam]
                                  · linarith only [h0, h223, hlam]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h200, h201, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p203_1]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h0, h168, hc12, hc23, hlam, hphi, p203_1]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  rcases p203_3 (m.d 0 2) (by simp) with h229 | h229
                                  · linarith only [h229, hlam, p203_0]
                                  · rcases p203_3 (m.d 1 2) (by simp) with h231 | h231
                                    · linarith only [h192, h231, hlam]
                                    · rcases p203_3 (m.d 2 3) (by simp) with h233 | h233
                                      · rcases p203_3 (m.d 2 4) (by simp) with h234 | h234
                                        · rcases p203_3 (m.d 2 5) (by simp) with h235 | h235
                                          · linarith only [h200, h235, hlam]
                                          · linarith only [h168, h235, hlam]
                                        · linarith only [h234, hlam, p203_0]
                                      · linarith only [h154, h233, hlam]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  rcases p203_3 (m.d 0 2) (by simp) with h240 | h240
                                  · linarith only [h156, h240, hlam]
                                  · linarith only [h0, h240, hlam]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h198, hlam, p203_1]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h0, h168, hc12, hc24, hlam, hphi, p203_1]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p203_1, u5elo2]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p203_1, u5elo2]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h199, hlam, p203_1]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [h200, hlam, p203_0]
                                · have p203_0 := h203c.1
                                  have p203_1 := h203c.2.1
                                  have p203_2 := h203c.2.2.1
                                  have p203_3 := h203c.2.2.2
                                  linarith only [hlam, p203_0]
                            · linarith only [h0, h156, h200, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h154, h199, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h1, h190, h198, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h189, h197, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1, h188, h196, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h188, h189, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h257 | h257
            · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
              · linarith only [h0, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h260 | h260
                · linarith only [h0, h1, h156, h188, h260, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h0, h168, h262, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h1, h188, h258, h264, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h264, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h0, h1, h257, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

end R2N4
