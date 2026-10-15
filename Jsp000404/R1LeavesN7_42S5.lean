import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
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
                      · linarith only [h0, h11, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h14, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h10, h16, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                          · linarith only [h1, h18, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h2, h20, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h0, h20, h4, h7, h9, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h24, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h23, h24, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                      · linarith only [h0, h27, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                        · linarith only [h0, h23, h29, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                          · linarith only [h1, h31, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                            · linarith only [h2, h33, h9, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                              · linarith only [h0, h23, h31, h35, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h0, h23, h35, h4, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
                  · linarith only [h38, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                      · linarith only [h0, h41, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h40, h41, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                      · linarith only [h0, h44, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                        · linarith only [h0, h4, h40, h46, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                          · linarith only [h0, h4, h40, h48, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · linarith only [h48, h7, h8, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
                · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                      · linarith only [h0, h54, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h5, h53, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                      · linarith only [h0, h57, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                        · linarith only [h0, h4, h53, h59, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                          · linarith only [h0, h4, h53, h61, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h63 | h63
                            · linarith only [h0, h5, h57, h63, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h52, h63, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · linarith only [h51, h52, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                      · linarith only [h0, h69, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h5, h68, h69, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                      · linarith only [h0, h72, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                        · linarith only [h0, h4, h68, h74, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                          · linarith only [h0, h4, h68, h7, h76, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                            · linarith only [h2, h78, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h67, h78, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                      · linarith only [h0, h82, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h5, h81, h82, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                      · linarith only [h4, h81, h85, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                        · linarith only [h0, h4, h81, h87, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                          · linarith only [h1, h89, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                            · linarith only [h2, h67, h7, h91, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                              · linarith only [h4, h7, h93, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                                · linarith only [h4, h51, h95, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                                  · linarith only [h0, h4, h5, h67, h7, h81, h97, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                                    · linarith only [h4, h67, h7, h81, h99, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h4, h7, h81, h99, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h102 | h102
              · rcases m.htr 0 3 5 (by decide) (by decide) with h103 | h103
                · linarith only [h103, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h105 | h105
                  · linarith only [h105, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
                      · linarith only [h0, h108, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h108, h5, h6, hc12, hc25, hlam, hphi]
                    · linarith only [h107, h4, h6, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
                · linarith only [h112, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h114 | h114
                  · linarith only [h114, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                      · linarith only [h0, h117, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h117, h5, h6, hc12, hc25, hlam, hphi]
                    · linarith only [h116, h4, h6, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h121 | h121
            · rcases m.htr 0 3 4 (by decide) (by decide) with h122 | h122
              · linarith only [h122, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
                · rcases m.htr 0 4 5 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                      · linarith only [h0, h127, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                          · linarith only [h1, h122, h124, h125, h130, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                            · linarith only [h132, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h125, h132, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                        · linarith only [h121, h126, h129, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h126, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h124, h125, h4, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                      · linarith only [h0, h140, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                          · linarith only [h1, h143, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                            · linarith only [h145, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h138, h145, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                        · linarith only [h121, h139, h142, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h139, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h121, h138, h5, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h151 | h151
              · linarith only [h151, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h153 | h153
                · linarith only [h121, h153, h4, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                      · linarith only [h0, h157, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                        · linarith only [h0, h121, h159, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                          · linarith only [h1, h151, h161, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                            · linarith only [h163, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h155, h163, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · linarith only [h121, h156, h4, hc12, hc25, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
                      · linarith only [h0, h168, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                        · linarith only [h0, h121, h170, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                          · linarith only [h1, h151, h172, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h174 | h174
                            · linarith only [h155, h174, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                              · linarith only [h0, h151, h167, h176, h5, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                                · linarith only [h0, h153, h155, h167, h178, h5, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                                  · linarith only [h0, h155, h167, h176, h180, h5, hc23, hc34, hlam, hphi]
                                  · linarith only [h0, h167, h180, h5, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h167, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h184 | h184
          · rcases m.htr 0 2 5 (by decide) (by decide) with h185 | h185
            · rcases m.htr 0 3 4 (by decide) (by decide) with h186 | h186
              · rcases m.htr 0 3 5 (by decide) (by decide) with h187 | h187
                · rcases m.htr 0 4 5 (by decide) (by decide) with h188 | h188
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
                    · linarith only [h0, h189, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
                      · linarith only [h0, h191, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h184, h191, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
                    · linarith only [h184, h194, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                      · linarith only [h1, h194, h196, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h184, h196, h4, hc12, hc23, hlam, hphi]
                · linarith only [h185, h187, h4, hlam]
              · linarith only [h184, h186, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h201 | h201
              · rcases m.htr 0 3 5 (by decide) (by decide) with h202 | h202
                · rcases m.htr 0 4 5 (by decide) (by decide) with h203 | h203
                  · linarith only [h184, h185, h203, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h205 | h205
                    · linarith only [h0, h205, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h207 | h207
                      · linarith only [h1, h205, h207, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h184, h207, h4, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h210 | h210
                  · linarith only [h184, h202, h210, h4, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h212 | h212
                    · linarith only [h0, h212, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h214 | h214
                      · linarith only [h1, h212, h214, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h184, h202, h214, h4, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h184, h201, h4, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h218 | h218
            · rcases m.htr 0 3 4 (by decide) (by decide) with h219 | h219
              · rcases m.htr 0 3 5 (by decide) (by decide) with h220 | h220
                · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                    · linarith only [h0, h222, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h224 | h224
                      · linarith only [h0, h184, h224, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                          · linarith only [h1, h227, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · linarith only [h1, h219, h222, h226, h227, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h218, h226, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h184, h218, h221, hlam]
                · linarith only [h184, h218, h219, h220, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h233 | h233
                · rcases m.htr 0 4 5 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
                    · linarith only [h0, h235, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
                      · linarith only [h0, h184, h218, h234, h237, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
                          · linarith only [h1, h219, h240, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                            · linarith only [h2, h242, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h234, h242, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                        · linarith only [h218, h239, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h184, h218, h234, hlam]
                · linarith only [h218, h233, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h248 | h248
              · rcases m.htr 0 3 5 (by decide) (by decide) with h249 | h249
                · rcases m.htr 0 4 5 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
                    · linarith only [h0, h251, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
                      · linarith only [h0, h184, h253, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
                        · linarith only [h0, h218, h255, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h257 | h257
                          · linarith only [h1, h257, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                            · linarith only [h2, h259, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h250, h259, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
                    · linarith only [h0, h248, h262, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h264 | h264
                      · linarith only [h1, h184, h262, h264, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h266 | h266
                        · linarith only [h0, h218, h250, h266, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h268 | h268
                          · linarith only [h1, h268, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h270 | h270
                            · linarith only [h2, h270, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h274 | h274
                                  · linarith only [h248, h250, h262, h268, h274, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h276 | h276
                                    · linarith only [h1, h248, h274, h276, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                                    · rcases h0bigk with h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        rcases p278_3 (m.d 0 1) (by simp) with h280 | h280
                                        · rcases p278_3 (m.d 0 2) (by simp) with h281 | h281
                                          · linarith only [h0, h281, hlam]
                                          · rcases p278_3 (m.d 0 3) (by simp) with h283 | h283
                                            · linarith only [h1, h283, hlam]
                                            · linarith only [h283, h4, hlam]
                                        · linarith only [h0, h280, hlam]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h249, h262, h268, h276, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p278_1, u0elo0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h248, h262, h268, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p278_1, u0elo0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h248, h250, h262, h268, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p278_1, u0elo0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h0, hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h4, hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h184, hlam, p278_1]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h218, hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h1, hlam, p278_1]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        rcases p278_3 (m.d 0 1) (by simp) with h296 | h296
                                        · rcases p278_3 (m.d 0 2) (by simp) with h297 | h297
                                          · linarith only [h297, h4, hlam]
                                          · rcases p278_3 (m.d 0 3) (by simp) with h299 | h299
                                            · rcases p278_3 (m.d 0 4) (by simp) with h300 | h300
                                              · linarith only [h248, h300, hlam]
                                              · linarith only [h184, h300, hlam]
                                            · linarith only [h299, h4, hlam]
                                        · linarith only [h0, h296, hlam]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h248, h262, h268, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p278_1, u0elo2]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h1, h248, h250, h262, h268, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p278_1, u0elo0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h2, hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h0, h184, h274, hc12, hc45, hlam, hphi, ht23, ht34, p278_1]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h248, hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h250, hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h3, hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        rcases p278_3 (m.d 0 1) (by simp) with h314 | h314
                                        · rcases p278_3 (m.d 0 2) (by simp) with h315 | h315
                                          · linarith only [h218, h315, hlam]
                                          · rcases p278_3 (m.d 0 3) (by simp) with h317 | h317
                                            · rcases p278_3 (m.d 0 4) (by simp) with h318 | h318
                                              · linarith only [h250, h318, hlam]
                                              · linarith only [h184, h318, hlam]
                                            · linarith only [h317, h4, hlam]
                                        · linarith only [h0, h314, hlam]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [h249, hlam, p278_0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht45, ht5b, p278_1, u0elo4, u4ehi0]
                                      · have p278_0 := h278c.1
                                        have p278_1 := h278c.2.1
                                        have p278_2 := h278c.2.2.1
                                        have p278_3 := h278c.2.2.2
                                        linarith only [hlam, p278_0]
                                · linarith only [h248, h262, h268, h273, h4, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h248, h272, h4, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
                  · linarith only [h248, h249, h328, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
                    · linarith only [h0, h248, h330, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h332 | h332
                      · linarith only [h0, h184, h332, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                        · linarith only [h0, h218, h248, h249, h334, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                          · linarith only [h1, h336, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · linarith only [h248, h249, h330, h336, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h339 | h339
                · rcases m.htr 0 4 5 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                    · linarith only [h0, h341, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
                      · linarith only [h0, h184, h340, h343, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h345 | h345
                        · linarith only [h0, h218, h345, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
                          · linarith only [h1, h347, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h349 | h349
                            · linarith only [h2, h349, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h340, h349, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · linarith only [h248, h339, h340, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h353 | h353
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h354 | h354
                    · linarith only [h0, h354, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
                      · linarith only [h0, h184, h356, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h358 | h358
                        · linarith only [h0, h218, h358, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
                          · linarith only [h1, h248, h360, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
                            · linarith only [h2, h362, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h353, h362, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
                    · linarith only [h0, h365, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h367 | h367
                      · linarith only [h0, h184, h367, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h369 | h369
                        · linarith only [h1, h218, h365, h369, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                          · linarith only [h1, h248, h371, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h373 | h373
                            · linarith only [h2, h373, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h376 | h376
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h377 | h377
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h378 | h378
                                    · linarith only [h353, h375, h378, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                                    · linarith only [h0, h248, h375, h377, h378, h4, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h381 | h381
                                    · linarith only [h0, h184, h377, h381, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h0bigk with h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        rcases p383_3 (m.d 0 1) (by simp) with h385 | h385
                                        · rcases p383_3 (m.d 0 2) (by simp) with h386 | h386
                                          · linarith only [h0, h386, hlam]
                                          · rcases p383_3 (m.d 0 3) (by simp) with h388 | h388
                                            · linarith only [h1, h388, hlam]
                                            · linarith only [h388, h4, hlam]
                                        · linarith only [h0, h385, hlam]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        rcases p383_3 (m.d 0 1) (by simp) with h392 | h392
                                        · rcases p383_3 (m.d 0 2) (by simp) with h393 | h393
                                          · linarith only [h0, h393, hlam]
                                          · rcases p383_3 (m.d 0 3) (by simp) with h395 | h395
                                            · linarith only [h1, h395, hlam]
                                            · rcases p383_3 (m.d 0 4) (by simp) with h397 | h397
                                              · linarith only [h2, h397, hlam]
                                              · linarith only [h248, h397, hlam]
                                        · linarith only [h1, h392, hlam]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, p383_1, u0elo0, u4ehi1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h2, h353, hlam, hphi, ht0b, ht45, ht5b, p383_1, u0elo0, u4ehi1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h0, hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h4, hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h184, hlam, p383_1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h218, hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h1, hlam, p383_1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h0, h248, h375, hc12, hc24, hlam, hphi, p383_1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h248, hlam, p383_1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h339, hlam, p383_1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h2, hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h0, h184, h377, hc12, hc45, hlam, hphi, ht23, ht34, p383_1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h184, h377, hc03, hc45, hlam, hphi, ht34, p383_1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h353, hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h3, hlam, p383_0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h0, h339, h376, hc12, hc23, hlam, hphi, p383_1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h0, h339, h376, h4, hc12, hc23, hlam, hphi, p383_1]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [h339, h376, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p383_1, u4ehi0]
                                      · have p383_0 := h383c.1
                                        have p383_1 := h383c.2.1
                                        have p383_2 := h383c.2.2.1
                                        have p383_3 := h383c.2.2.2
                                        linarith only [hlam, p383_0]
                                · linarith only [h248, h375, h376, hc03, hc35, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h424 | h424
                                · linarith only [h0, h339, h375, h4, h424, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h426 | h426
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h427 | h427
                                    · rcases h0bigk with h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        rcases p428_3 (m.d 0 1) (by simp) with h430 | h430
                                        · rcases p428_3 (m.d 0 2) (by simp) with h431 | h431
                                          · linarith only [h0, h431, hlam]
                                          · rcases p428_3 (m.d 0 3) (by simp) with h433 | h433
                                            · linarith only [h1, h433, hlam]
                                            · linarith only [h4, h433, hlam]
                                        · linarith only [h0, h430, hlam]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        rcases p428_3 (m.d 0 1) (by simp) with h437 | h437
                                        · rcases p428_3 (m.d 0 2) (by simp) with h438 | h438
                                          · linarith only [h0, h438, hlam]
                                          · rcases p428_3 (m.d 0 3) (by simp) with h440 | h440
                                            · linarith only [h1, h440, hlam]
                                            · rcases p428_3 (m.d 0 4) (by simp) with h442 | h442
                                              · linarith only [h2, h442, hlam]
                                              · linarith only [h248, h442, hlam]
                                        · linarith only [h1, h437, hlam]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, p428_1, u0elo0, u4ehi1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h3, h373, hlam, hphi, ht0b, ht45, ht5b, p428_1, u0elo0, u4ehi1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h0, hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h4, hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h184, hlam, p428_1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h218, hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h1, hlam, p428_1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h0, h4, h424, h427, hc12, hc34, hlam, hphi, ht23, p428_1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h248, hlam, p428_1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h339, hlam, p428_1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h2, hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h0, h353, h375, h426, hc12, hc34, hlam, hphi, ht23, p428_1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h353, h375, h426, hc03, hc34, hlam, hphi, p428_1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h353, hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h3, hlam, p428_0]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h0, h353, h375, h426, hc12, hc34, hlam, hphi, ht23, p428_1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h1, h353, h365, h375, h426, hc12, hc34, hlam, hphi, ht23, p428_1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [h2, h353, h375, h426, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p428_1, u4ehi1]
                                      · have p428_0 := h428c.1
                                        have p428_1 := h428c.2.1
                                        have p428_2 := h428c.2.2.1
                                        have p428_3 := h428c.2.2.2
                                        linarith only [hlam, p428_0]
                                    · linarith only [h375, h426, h427, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h469 | h469
                                    · linarith only [h0, h375, h4, h426, h469, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h375, h4, h469, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h472 | h472
        · rcases m.htr 0 2 4 (by decide) (by decide) with h473 | h473
          · rcases m.htr 0 2 5 (by decide) (by decide) with h474 | h474
            · linarith only [h0, h3, h474, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h476 | h476
              · rcases m.htr 0 3 5 (by decide) (by decide) with h477 | h477
                · linarith only [h0, h3, h472, h477, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h479 | h479
                  · linarith only [h0, h3, h472, h476, h479, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h481 | h481
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h482 | h482
                      · linarith only [h0, h3, h482, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi2]
                      · linarith only [h473, h474, h482, hc12, hc25, hlam, hphi]
                    · linarith only [h472, h474, h481, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h486 | h486
                · linarith only [h0, h3, h473, h476, h486, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
                  · linarith only [h0, h3, h473, h488, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h491 | h491
                      · linarith only [h0, h491, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h473, h474, h491, hc12, hc25, hlam, hphi]
                    · linarith only [h472, h474, h490, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h495 | h495
            · linarith only [h0, h3, h495, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h497 | h497
              · linarith only [h472, h473, h497, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h499 | h499
                · linarith only [h2, h3, h472, h473, h499, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h501 | h501
                  · linarith only [h2, h3, h501, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
                      · linarith only [h0, h473, h504, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h506 | h506
                        · linarith only [h0, h3, h495, h506, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
                          · linarith only [h1, h3, h506, h508, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h510 | h510
                            · linarith only [h2, h3, h501, h510, hlam]
                            · linarith only [h2, h3, h503, h504, h510, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h472, h473, h503, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h514 | h514
          · rcases m.htr 0 2 5 (by decide) (by decide) with h515 | h515
            · linarith only [h1, h3, h472, h515, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h517 | h517
              · rcases m.htr 0 3 5 (by decide) (by decide) with h518 | h518
                · linarith only [h1, h3, h518, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h520 | h520
                  · linarith only [h0, h3, h514, h520, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
                    · linarith only [h472, h514, h522, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
                      · linarith only [h1, h522, h524, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h472, h514, h524, hc12, hc23, hlam, hphi]
              · linarith only [h472, h514, h517, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h528 | h528
            · linarith only [h0, h3, h528, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h530 | h530
              · rcases m.htr 0 3 5 (by decide) (by decide) with h531 | h531
                · linarith only [h1, h3, h531, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h533 | h533
                  · linarith only [h1, h3, h530, h533, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                    · linarith only [h0, h472, h535, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h537 | h537
                      · linarith only [h0, h514, h537, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h539 | h539
                        · linarith only [h0, h3, h528, h539, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h541 | h541
                          · linarith only [h1, h541, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · linarith only [h530, h531, h535, h541, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h544 | h544
                · linarith only [h2, h3, h530, h544, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h546 | h546
                  · linarith only [h2, h3, h546, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
                    · linarith only [h0, h472, h548, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h550 | h550
                      · linarith only [h0, h3, h550, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h552 | h552
                        · linarith only [h0, h528, h552, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
                          · linarith only [h1, h3, h472, h530, h552, h554, hc02, hc25, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h556 | h556
                            · linarith only [h2, h3, h546, h556, hlam]
                            · linarith only [h2, h3, h556, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h559 | h559
      · rcases m.htr 0 2 3 (by decide) (by decide) with h560 | h560
        · rcases m.htr 0 2 4 (by decide) (by decide) with h561 | h561
          · linarith only [h0, h2, h561, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h563 | h563
            · rcases m.htr 0 3 4 (by decide) (by decide) with h564 | h564
              · linarith only [h1, h2, h564, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h566 | h566
                · rcases m.htr 0 4 5 (by decide) (by decide) with h567 | h567
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h569 | h569
                      · linarith only [h0, h2, h561, h569, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h571 | h571
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h572 | h572
                          · linarith only [h0, h1, h2, h560, h564, h568, h572, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h2, h568, h572, hc23, hc34, hlam, hphi]
                        · linarith only [h563, h568, h571, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h560, h561, h568, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h560, h566, h567, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h578 | h578
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h579 | h579
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h580 | h580
                      · linarith only [h0, h2, h561, h580, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h582 | h582
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h583 | h583
                          · linarith only [h1, h2, h580, h583, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h0, h2, h579, h583, hc23, hc34, hlam, hphi]
                        · linarith only [h563, h579, h582, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h560, h561, h579, hc12, hc24, hlam, hphi]
                  · linarith only [h2, h559, h578, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h589 | h589
              · linarith only [h2, h559, h560, h563, h589, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h591 | h591
                · linarith only [h560, h563, h591, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h593 | h593
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h594 | h594
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h595 | h595
                      · linarith only [h0, h2, h595, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h597 | h597
                        · linarith only [h0, h2, h563, h595, h597, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h599 | h599
                          · linarith only [h0, h589, h593, h594, h599, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · linarith only [h2, h559, h594, h597, h599, hc23, hc34, hlam, hphi]
                    · linarith only [h560, h563, h594, hc12, hc25, hlam, hphi]
                  · linarith only [h2, h559, h593, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h604 | h604
          · linarith only [h1, h2, h560, h604, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h606 | h606
            · rcases m.htr 0 3 4 (by decide) (by decide) with h607 | h607
              · linarith only [h1, h2, h607, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h609 | h609
                · rcases m.htr 0 4 5 (by decide) (by decide) with h610 | h610
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h611 | h611
                    · linarith only [h0, h560, h611, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h613 | h613
                      · linarith only [h0, h2, h604, h613, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h615 | h615
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h616 | h616
                          · linarith only [h1, h560, h607, h616, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h618 | h618
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h619 | h619
                              · linarith only [h1, h2, h611, h615, h616, h618, h619, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h621 | h621
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h622 | h622
                                  · linarith only [h560, h606, h619, h622, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                                  · linarith only [h1, h2, h611, h613, h615, h618, h622, hlam]
                                · linarith only [h560, h609, h621, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1, h2, h606, h610, h611, h615, h618, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h1, h2, h560, h606, h613, h615, hc12, hc24, hlam, hphi]
                  · linarith only [h1, h2, h560, h606, h610, hlam]
                · linarith only [h560, h606, h609, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h630 | h630
              · linarith only [h1, h2, h630, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h632 | h632
                · rcases m.htr 0 4 5 (by decide) (by decide) with h633 | h633
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
                    · linarith only [h0, h560, h634, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
                      · linarith only [h0, h560, h604, h633, h636, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h638 | h638
                        · linarith only [h1, h2, h606, h634, h636, h638, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
                          · linarith only [h1, h2, h630, h636, h640, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h642 | h642
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                              · linarith only [h0, h2, h640, h643, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h645 | h645
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h646 | h646
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h647 | h647
                                    · rcases h0bigk with h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [hlam, p648_0]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h0, h2, h636, hc12, hc24, hlam, hphi, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h2, h636, h643, hc03, hc34, hlam, hphi, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h2, hlam, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h0, h2, h606, h636, h643, hc12, hc34, hlam, hphi, ht23, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h0, hlam, p648_0]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [hlam, p648_0]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h560, hlam, p648_0]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h604, hlam, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h606, hlam, p648_0]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h1, hlam, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h0, h1, h2, h636, h643, hc12, hc34, hlam, hphi, ht23, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [hlam, p648_0]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h630, hlam, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h0, h1, h2, h606, h636, h643, hc12, hc34, hlam, hphi, ht23, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h1, h632, h647, hlam, hphi, ht0b, ht45, ht5b, p648_1, u0elo3, u4ehi4]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        rcases p648_3 (m.d 0 1) (by simp) with h665 | h665
                                        · linarith only [h2, h665, hlam]
                                        · linarith only [h0, h665, hlam]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h632, h647, hlam, hphi, ht0b, ht45, ht5b, p648_1, u0elo3, u4ehi4]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [hlam, p648_0]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h632, h647, hlam, hphi, ht0b, ht45, ht5b, p648_1, u0elo3, u4ehi4]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h559, hlam, p648_0]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h0, h2, h559, h636, h643, hc12, hc34, hlam, hphi, ht23, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h632, hlam, p648_0]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [h633, hlam, p648_1]
                                      · have p648_0 := h648c.1
                                        have p648_1 := h648c.2.1
                                        have p648_2 := h648c.2.2.1
                                        have p648_3 := h648c.2.2.2
                                        linarith only [hlam, p648_0]
                                    · linarith only [h1, h2, h636, h643, h647, hc13, hc45, hlam, hphi, ht34]
                                  · linarith only [h2, h559, h636, h642, h646, hlam]
                                · linarith only [h1, h2, h632, h636, h643, h645, hc23, hc34, hlam, hphi]
                            · linarith only [h1, h2, h634, h642, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h1, h2, h632, h633, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h681 | h681
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h682 | h682
                    · linarith only [h0, h560, h682, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h684 | h684
                      · linarith only [h0, h604, h681, h684, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h686 | h686
                        · linarith only [h1, h606, h682, h686, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h688 | h688
                          · linarith only [h1, h2, h630, h684, h688, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h690 | h690
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h691 | h691
                              · linarith only [h0, h2, h688, h691, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h693 | h693
                                · linarith only [h0, h560, h632, h691, h693, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h695 | h695
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h696 | h696
                                    · rcases h0bigk with h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [hlam, p697_0]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h0, h2, h684, hc12, hc24, hlam, hphi, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h0, h2, h560, h684, hc12, hc24, hlam, hphi, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h2, hlam, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h2, h559, h684, h690, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p697_1, u4ehi4]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h0, hlam, p697_0]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [hlam, p697_0]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h560, hlam, p697_0]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h604, hlam, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h606, hlam, p697_0]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h1, hlam, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h0, h1, h2, h684, hc12, hc24, hlam, hphi, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [hlam, p697_0]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h630, hlam, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h632, hlam, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p697_1, u0elo3]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        rcases p697_3 (m.d 0 1) (by simp) with h714 | h714
                                        · linarith only [h2, h714, hlam]
                                        · linarith only [h0, h714, hlam]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        rcases p697_3 (m.d 0 1) (by simp) with h717 | h717
                                        · linarith only [h2, h717, hlam]
                                        · linarith only [h1, h717, hlam]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [hlam, p697_0]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h559, h690, hlam, hphi, ht0b, ht45, ht5b, p697_1, u0elo3, u4ehi4]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h559, hlam, p697_0]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h0, h2, h559, h684, h691, hc12, hc34, hlam, hphi, ht23, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h2, h559, h684, h691, hc03, hc34, hlam, hphi, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [h681, hlam, p697_1]
                                      · have p697_0 := h697c.1
                                        have p697_1 := h697c.2.1
                                        have p697_2 := h697c.2.2.1
                                        have p697_3 := h697c.2.2.2
                                        linarith only [hlam, p697_0]
                                    · linarith only [h2, h559, h684, h690, h691, h696, hlam]
                                  · linarith only [h2, h559, h684, h690, h695, hlam]
                            · linarith only [h0, h2, h690, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h2, h559, h681, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h731 | h731
        · rcases m.htr 0 2 4 (by decide) (by decide) with h732 | h732
          · linarith only [h0, h2, h732, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h734 | h734
            · linarith only [h0, h559, h734, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h736 | h736
              · linarith only [h1, h2, h736, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h738 | h738
                · linarith only [h0, h559, h731, h738, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h740 | h740
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h741 | h741
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
                      · linarith only [h0, h732, h742, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h744 | h744
                        · linarith only [h0, h559, h734, h744, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h746 | h746
                          · linarith only [h0, h2, h736, h741, h742, h746, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h2, h741, h746, hc23, hc34, hlam, hphi]
                    · linarith only [h731, h732, h741, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h750 | h750
                    · linarith only [h0, h2, h740, h750, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h2, h731, h740, h750, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h753 | h753
          · linarith only [h0, h2, h753, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h755 | h755
            · linarith only [h1, h559, h731, h755, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h757 | h757
              · linarith only [h1, h2, h757, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h759 | h759
                · linarith only [h1, h559, h759, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h761 | h761
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h762 | h762
                    · linarith only [h0, h559, h731, h761, h762, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h764 | h764
                      · linarith only [h0, h753, h761, h764, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h766 | h766
                        · linarith only [h0, h559, h755, h766, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h768 | h768
                          · linarith only [h1, h768, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h770 | h770
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h771 | h771
                              · linarith only [h1, h559, h762, h768, h770, h771, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h773 | h773
                                · linarith only [h759, h771, h773, hc03, hc34, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h775 | h775
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h776 | h776
                                    · rcases h0bigk with h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [hlam, p777_0]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h559, h764, h770, hc02, hc24, hlam, hphi, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h1, h559, h762, h764, h770, hc12, hc24, hlam, hphi, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h2, hlam, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h559, hlam, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h0, hlam, p777_0]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [hlam, p777_0]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h731, hlam, p777_0]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h753, hlam, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h755, hlam, p777_0]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h1, hlam, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h0, h1, h559, h764, h770, hc12, hc24, hlam, hphi, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [hlam, p777_0]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h757, hlam, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h759, hlam, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1, u0elo3]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        rcases p777_3 (m.d 0 1) (by simp) with h794 | h794
                                        · linarith only [h2, h794, hlam]
                                        · linarith only [h0, h794, hlam]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        rcases p777_3 (m.d 0 1) (by simp) with h797 | h797
                                        · linarith only [h2, h797, hlam]
                                        · linarith only [h1, h797, hlam]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [hlam, p777_0]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h1, h559, h762, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1, u0elo3]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h1, h762, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1, u0elo4]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        rcases p777_3 (m.d 0 1) (by simp) with h803 | h803
                                        · linarith only [h559, h803, hlam]
                                        · linarith only [h0, h803, hlam]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        rcases p777_3 (m.d 0 1) (by simp) with h806 | h806
                                        · linarith only [h559, h806, hlam]
                                        · linarith only [h1, h806, hlam]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [h761, hlam, p777_1]
                                      · have p777_0 := h777c.1
                                        have p777_1 := h777c.2.1
                                        have p777_2 := h777c.2.2.1
                                        have p777_3 := h777c.2.2.2
                                        linarith only [hlam, p777_0]
                                    · linarith only [h1, h2, h762, h764, h771, h776, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h2, h761, h764, h775, hlam]
                            · linarith only [h2, h761, h770, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h814 | h814
                    · linarith only [h0, h2, h761, h814, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h816 | h816
                      · linarith only [h1, h2, h761, h814, h816, hc45, hlam, hphi, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h818 | h818
                        · linarith only [h0, h755, h818, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h820 | h820
                          · linarith only [h1, h820, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h822 | h822
                            · linarith only [h1, h2, h761, h814, h816, h822, hc12, hc24, hlam, hphi]
                            · linarith only [h1, h2, h814, h822, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h825 | h825
    · rcases m.htr 0 1 5 (by decide) (by decide) with h826 | h826
      · rcases m.htr 0 2 3 (by decide) (by decide) with h827 | h827
        · linarith only [h0, h1, h827, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h829 | h829
          · rcases m.htr 0 2 5 (by decide) (by decide) with h830 | h830
            · rcases m.htr 0 3 4 (by decide) (by decide) with h831 | h831
              · rcases m.htr 0 3 5 (by decide) (by decide) with h832 | h832
                · rcases m.htr 0 4 5 (by decide) (by decide) with h833 | h833
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h834 | h834
                    · linarith only [h827, h829, h833, h834, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h836 | h836
                      · linarith only [h0, h836, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h1, h829, h834, h836, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h839 | h839
                    · linarith only [h0, h1, h827, h839, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h841 | h841
                      · linarith only [h0, h1, h839, h841, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h1, h829, h839, h841, hc12, hc23, hlam, hphi]
                · linarith only [h1, h826, h832, hlam]
              · linarith only [h1, h825, h831, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h846 | h846
              · rcases m.htr 0 3 5 (by decide) (by decide) with h847 | h847
                · rcases m.htr 0 4 5 (by decide) (by decide) with h848 | h848
                  · linarith only [h829, h830, h848, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
                    · linarith only [h0, h827, h850, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h852 | h852
                      · linarith only [h0, h1, h850, h852, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h829, h830, h852, hc12, hc25, hlam, hphi]
                · linarith only [h1, h826, h847, hlam]
              · linarith only [h1, h825, h846, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h857 | h857
            · rcases m.htr 0 3 4 (by decide) (by decide) with h858 | h858
              · rcases m.htr 0 3 5 (by decide) (by decide) with h859 | h859
                · rcases m.htr 0 4 5 (by decide) (by decide) with h860 | h860
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h861 | h861
                    · linarith only [h0, h827, h861, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h863 | h863
                      · linarith only [h0, h1, h829, h861, h863, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h865 | h865
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h866 | h866
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h867 | h867
                            · linarith only [h1, h825, h861, h867, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h1, h825, h860, h861, h863, h867, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h825, h860, h866, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h829, h857, h865, hc12, hc24, hlam, hphi]
                  · linarith only [h829, h857, h860, hlam]
                · linarith only [h1, h825, h829, h857, h859, hlam]
              · linarith only [h1, h825, h858, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h875 | h875
              · rcases m.htr 0 3 5 (by decide) (by decide) with h876 | h876
                · rcases m.htr 0 4 5 (by decide) (by decide) with h877 | h877
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                    · linarith only [h0, h827, h878, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h880 | h880
                      · linarith only [h0, h829, h877, h880, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h882 | h882
                        · linarith only [h0, h857, h882, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h884 | h884
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h885 | h885
                            · linarith only [h1, h825, h878, h885, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h1, h825, h877, h878, h885, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                          · linarith only [h1, h825, h880, h884, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h889 | h889
                    · linarith only [h0, h1, h827, h889, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h891 | h891
                      · linarith only [h0, h829, h891, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h893 | h893
                        · linarith only [h0, h857, h893, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h895 | h895
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h896 | h896
                            · linarith only [h825, h877, h896, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h898 | h898
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h899 | h899
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h900 | h900
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h901 | h901
                                    · linarith only [h825, h877, h895, h901, hlam]
                                    · rcases h0bigk with h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h1, h889, hc02, hc23, hlam, hphi, p903_1]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h1, hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h1, h825, h889, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p903_1, u4ehi3]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h1, h825, h877, h889, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p903_1, u4ehi3]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h0, hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h827, hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h829, hlam, p903_1]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h857, hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p903_1, u0elo2]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        rcases p903_3 (m.d 0 1) (by simp) with h915 | h915
                                        · linarith only [h1, h915, hlam]
                                        · linarith only [h0, h915, hlam]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h825, h895, hlam, hphi, ht0b, ht45, ht5b, p903_1, u0elo2, u4ehi3]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h825, h877, h895, hlam, hphi, ht0b, ht45, ht5b, p903_1, u0elo2, u4ehi3]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h825, hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h0, h877, h900, hc12, hc24, hlam, hphi, p903_1]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h875, hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h877, hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h826, hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h0, h1, h826, h889, hc12, hc23, hlam, hphi, p903_1]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h876, hlam, p903_0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [h1, h826, h889, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p903_1, u4ehi0]
                                      · have p903_0 := h903c.1
                                        have p903_1 := h903c.2.1
                                        have p903_2 := h903c.2.2.1
                                        have p903_3 := h903c.2.2.2
                                        linarith only [hlam, p903_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h931 | h931
                                    · linarith only [h1, h826, h889, h895, h896, h900, h931, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                                    · rcases h0bigk with h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h0, h1, h889, hc12, hc23, hlam, hphi, p933_1]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h1, hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h1, h889, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p933_1, u4ehi0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h0, h1, h857, h889, hc12, hc23, hlam, hphi, p933_1]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h0, hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h827, hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h829, hlam, p933_1]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h857, hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p933_1, u0elo2]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        rcases p933_3 (m.d 0 1) (by simp) with h945 | h945
                                        · linarith only [h1, h945, hlam]
                                        · linarith only [h0, h945, hlam]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h825, h895, hlam, hphi, ht0b, ht45, ht5b, p933_1, u0elo2, u4ehi3]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h825, h877, h895, hlam, hphi, ht0b, ht45, ht5b, p933_1, u0elo2, u4ehi3]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h825, hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h0, h1, h825, h889, hc12, hc23, hlam, hphi, p933_1]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h875, hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h877, hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h826, hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h0, h1, h826, h889, hc12, hc23, hlam, hphi, p933_1]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h876, hlam, p933_0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [h1, h826, h889, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p933_1, u4ehi0]
                                      · have p933_0 := h933c.1
                                        have p933_1 := h933c.2.1
                                        have p933_2 := h933c.2.2.1
                                        have p933_3 := h933c.2.2.2
                                        linarith only [hlam, p933_0]
                                · linarith only [h1, h876, h889, h899, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h1, h826, h889, h895, h896, h898, hlam]
                          · linarith only [h0, h1, h895, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h826, h876, hlam]
              · linarith only [h1, h825, h875, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h966 | h966
        · linarith only [h0, h1, h966, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h968 | h968
          · rcases m.htr 0 2 5 (by decide) (by decide) with h969 | h969
            · linarith only [h0, h826, h969, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h971 | h971
              · rcases m.htr 0 3 5 (by decide) (by decide) with h972 | h972
                · rcases m.htr 0 4 5 (by decide) (by decide) with h973 | h973
                  · linarith only [h0, h826, h968, h973, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h975 | h975
                    · linarith only [h0, h966, h975, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h977 | h977
                      · linarith only [h0, h1, h975, h977, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h968, h969, h977, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h980 | h980
                  · linarith only [h825, h826, h980, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h982 | h982
                    · linarith only [h0, h1, h972, h982, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h984 | h984
                      · linarith only [h0, h1, h972, h984, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h1, h968, h972, h984, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1, h825, h971, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h988 | h988
            · linarith only [h825, h826, h968, h988, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h990 | h990
              · rcases m.htr 0 3 5 (by decide) (by decide) with h991 | h991
                · rcases m.htr 0 4 5 (by decide) (by decide) with h992 | h992
                  · linarith only [h825, h826, h992, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h994 | h994
                    · linarith only [h0, h966, h994, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h996 | h996
                      · linarith only [h0, h1, h968, h994, h996, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h998 | h998
                        · linarith only [h825, h826, h988, h996, h998, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1000 | h1000
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1001 | h1001
                            · linarith only [h1, h1001, h825, h994, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h1001, h825, h826, hc45, hlam, hphi, u4ehi1]
                          · linarith only [h1, h1000, h825, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1005 | h1005
                  · linarith only [h1, h1005, h825, h991, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1007 | h1007
                    · linarith only [h0, h1007, h966, h968, h990, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1009 | h1009
                      · linarith only [h0, h1, h1009, h991, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1011 | h1011
                        · linarith only [h1, h1009, h1011, h825, h988, h991, hc02, hc35, hlam, hphi, ht23]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1013 | h1013
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1014 | h1014
                            · linarith only [h1, h1005, h1014, h825, h991, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                            · linarith only [h1013, h1014, h825, h826, hc45, hlam, hphi, u4ehi3]
                          · linarith only [h1, h1013, h825, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h1, h825, h990, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1019 | h1019
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1020 | h1020
        · linarith only [h0, h1, h1020, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1022 | h1022
          · linarith only [h0, h1022, h825, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1024 | h1024
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1025 | h1025
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1026 | h1026
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1027 | h1027
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1028 | h1028
                    · linarith only [h0, h1020, h1028, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1030 | h1030
                      · linarith only [h0, h1, h1022, h1028, h1030, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1032 | h1032
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1033 | h1033
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1034 | h1034
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1035 | h1035
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1036 | h1036
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1037 | h1037
                                  · linarith only [h0, h1028, h1032, h1033, h1037, h825, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                  · linarith only [h0, h1019, h1030, h1034, h1037, h825, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                                · linarith only [h0, h1028, h1032, h1033, h1034, h1036, h825, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h1028, h1032, h1033, h1034, h1035, h825, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h1034, h825, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h1025, h1032, h1033, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h0, h1, h1024, h1028, h1032, hc12, hc23, hlam, hphi]
                  · linarith only [h1019, h1027, h825, hlam]
                · linarith only [h0, h1, h1024, h1026, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1047 | h1047
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1048 | h1048
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1049 | h1049
                    · linarith only [h0, h1, h1025, h1049, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1051 | h1051
                      · linarith only [h0, h1, h1025, h1051, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1053 | h1053
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1054 | h1054
                          · linarith only [h0, h1, h1025, h1049, h1054, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h1053, h1054, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1024, h1051, h1053, h825, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h1, h1024, h1025, h1048, hlam]
                · linarith only [h0, h1, h1024, h1047, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1060 | h1060
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1061 | h1061
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1062 | h1062
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1063 | h1063
                    · linarith only [h0, h1020, h1063, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1065 | h1065
                      · linarith only [h0, h1, h1063, h1065, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1067 | h1067
                        · linarith only [h0, h1024, h1067, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1069 | h1069
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1070 | h1070
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1071 | h1071
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1072 | h1072
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1073 | h1073
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1074 | h1074
                                    · linarith only [h1060, h1074, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                    · linarith only [h1062, h1074, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                  · linarith only [h1019, h1065, h1070, h1073, h825, hlam]
                                · linarith only [h1061, h1063, h1069, h1072, h825, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h1019, h1063, h1069, h1070, h1071, h825, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h1070, h825, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h1019, h1067, h1069, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1019, h1062, h825, hlam]
                · linarith only [h1, h1019, h1061, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1084 | h1084
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1085 | h1085
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1086 | h1086
                    · linarith only [h0, h1, h1020, h1086, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1088 | h1088
                      · linarith only [h0, h1022, h1085, h1088, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1090 | h1090
                        · linarith only [h0, h1, h1024, h1060, h1090, hc02, hc34, hlam, hphi, ht23]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1092 | h1092
                          · linarith only [h0, h1, h1060, h1086, h1092, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h1019, h1090, h1092, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1019, h1085, h825, hlam]
                · linarith only [h1, h1019, h1084, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1097 | h1097
        · linarith only [h0, h1, h1097, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1099 | h1099
          · linarith only [h0, h1099, h825, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1101 | h1101
            · linarith only [h0, h1019, h1101, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1103 | h1103
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1104 | h1104
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1105 | h1105
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1106 | h1106
                    · linarith only [h0, h1019, h1097, h1103, h1105, h1106, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1108 | h1108
                      · linarith only [h0, h1099, h1105, h1108, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1110 | h1110
                        · linarith only [h0, h1101, h1110, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1112 | h1112
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1113 | h1113
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1114 | h1114
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1115 | h1115
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1116 | h1116
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1117 | h1117
                                    · linarith only [h1103, h1117, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                    · linarith only [h1103, h1105, h1117, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
                                  · linarith only [h1019, h1103, h1105, h1108, h1113, h1116, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h1, h1104, h1106, h1115, hlam]
                              · linarith only [h0, h1, h1106, h1114, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1103, h1105, h1113, h825, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1, h1103, h1112, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1125 | h1125
                    · linarith only [h0, h1105, h1125, h825, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1127 | h1127
                      · linarith only [h0, h1105, h1127, h825, hc45, hlam, hphi, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1129 | h1129
                        · linarith only [h0, h1101, h1129, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1131 | h1131
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1132 | h1132
                            · linarith only [h0, h1105, h1125, h1131, h1132, h825, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1132, h825, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h1103, h1131, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1136 | h1136
                  · linarith only [h1103, h1104, h1136, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1138 | h1138
                    · linarith only [h0, h1, h1104, h1138, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1140 | h1140
                      · linarith only [h0, h1099, h1140, h825, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1142 | h1142
                        · linarith only [h0, h1101, h1142, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1144 | h1144
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1145 | h1145
                            · linarith only [h0, h1136, h1138, h1144, h1145, h825, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1145, h825, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1103, h1104, h1144, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1149 | h1149
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1150 | h1150
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1151 | h1151
                    · linarith only [h0, h1, h1103, h1151, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1153 | h1153
                      · linarith only [h0, h1019, h1103, h1149, h1153, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1155 | h1155
                        · linarith only [h0, h1101, h1155, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1157 | h1157
                          · linarith only [h0, h1019, h1103, h1149, h1151, h1157, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h1157, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1103, h1149, h1150, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1161 | h1161
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1162 | h1162
                    · linarith only [h0, h1, h1149, h1162, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1164 | h1164
                      · linarith only [h0, h1, h1149, h1164, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1166 | h1166
                        · linarith only [h0, h1101, h1166, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1168 | h1168
                          · linarith only [h0, h1, h1103, h1162, h1168, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h1168, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1171 | h1171
                    · linarith only [h0, h1, h1149, h1171, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1173 | h1173
                      · linarith only [h0, h1, h1103, h1161, h1173, hc45, hlam, hphi, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1175 | h1175
                        · linarith only [h0, h1, h1101, h1103, h1161, h1175, hc02, hc45, hlam, hphi, ht23, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1177 | h1177
                          · linarith only [h0, h1, h1103, h1171, h1177, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h1177, hc12, hc34, hlam, hphi, ht23]

end R2N4
