import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_I_L_0_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                      · linarith only [h0, h11, h3, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h0, h13, h3, h9, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h15, h3, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h0, h15, h3, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                      · linarith only [h0, h18, h20, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h0, h18, h22, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                          · linarith only [h1, h24, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h0, h24, h3, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h28 | h28
                · linarith only [h28, h6, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h31, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                      · linarith only [h0, h3, h31, h33, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                        · linarith only [h0, h3, h31, h35, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                          · linarith only [h37, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                            · linarith only [h28, h3, h31, h39, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                                · linarith only [h28, h3, h42, hc35, hlam, hphi, u3ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
                                  · linarith only [h0, h28, h3, h44, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                                      · rcases h0emin with h48 | h48 | h48 | h48 | h48
                                        · linarith only [h48, hlam, ht01, u1elo0]
                                        · linarith only [h0, h48, hlam, ht01, u1elo0]
                                        · linarith only [h28, h47, h48, hc34, hlam, ht01, ht12, ht23]
                                        · linarith only [h2, h48, hlam, ht01, u1elo0]
                                        · linarith only [h0, h48, h5, hlam, ht01, u1elo0]
                                      · linarith only [h0, h33, h4, h41, h47, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h33, h41, h46, hlam]
                              · linarith only [h0, h30, h37, h4, h41, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                    · linarith only [h0, h57, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                      · linarith only [h0, h3, h57, h59, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                        · linarith only [h0, h3, h57, h61, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                          · linarith only [h3, h57, h6, h63, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                            · linarith only [h28, h65, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                              · linarith only [h0, h30, h4, h59, h67, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                                · linarith only [h3, h6, h69, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                                  · linarith only [h28, h3, h71, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
                                    · linarith only [h30, h4, h73, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                                      · linarith only [h2, h30, h63, h75, hc34, hlam, hphi, u3ehi1]
                                      · linarith only [h3, h57, h6, h75, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h78 | h78
              · rcases m.htr 0 3 5 (by decide) (by decide) with h79 | h79
                · linarith only [h3, h5, h79, hlam]
                · linarith only [h78, h79, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h82 | h82
                · linarith only [h78, h82, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h84 | h84
                  · linarith only [h4, h5, h84, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
                    · linarith only [h0, h86, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · linarith only [h3, h5, h86, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h89 | h89
            · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
              · linarith only [h3, h4, h90, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h92 | h92
                · linarith only [h90, h92, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                    · linarith only [h0, h95, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · linarith only [h3, h4, h95, hc12, hc24, hlam, hphi]
                  · linarith only [h3, h4, h94, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h99 | h99
              · linarith only [h3, h4, h99, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h99, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                    · linarith only [h0, h104, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · linarith only [h104, h3, h89, hc12, hc25, hlam, hphi]
                  · linarith only [h103, h3, h4, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h108 | h108
          · rcases m.htr 0 2 5 (by decide) (by decide) with h109 | h109
            · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
              · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
                · rcases m.htr 0 4 5 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
                    · linarith only [h108, h113, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                          · linarith only [h1, h117, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h1, h110, h117, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                        · linarith only [h109, h116, h3, hc12, hc23, hlam, hphi]
                      · linarith only [h108, h115, h3, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                    · linarith only [h108, h122, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                          · linarith only [h1, h126, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h110, h112, h126, hc45, hlam, hphi, ht34, u3ehi1]
                        · linarith only [h109, h125, h3, hc12, hc23, hlam, hphi]
                      · linarith only [h108, h124, h3, hc12, hc23, hlam, hphi]
                · linarith only [h110, h111, hc35, hlam, hphi, u3ehi3]
              · linarith only [h108, h110, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h133 | h133
              · rcases m.htr 0 3 5 (by decide) (by decide) with h134 | h134
                · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
                  · linarith only [h108, h109, h135, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                    · linarith only [h108, h137, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h140 | h140
                        · linarith only [h0, h109, h140, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h142 | h142
                          · linarith only [h1, h142, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h133, h135, h142, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h108, h139, h3, hc12, hc23, hlam, hphi]
                · linarith only [h133, h134, hc35, hlam, hphi, u3ehi3]
              · linarith only [h108, h133, h3, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h148 | h148
            · rcases m.htr 0 3 4 (by decide) (by decide) with h149 | h149
              · rcases m.htr 0 3 5 (by decide) (by decide) with h150 | h150
                · rcases m.htr 0 4 5 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
                    · linarith only [h148, h152, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
                      · linarith only [h1, h108, h148, h150, h152, h154, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                          · linarith only [h1, h157, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h1, h149, h157, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                        · linarith only [h108, h148, h156, hc12, hc24, hlam, hphi]
                  · linarith only [h108, h148, h151, hlam]
                · linarith only [h149, h150, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                · linarith only [h149, h163, hc34, hlam, hphi, u3ehi4]
                · linarith only [h148, h163, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h166 | h166
              · rcases m.htr 0 3 5 (by decide) (by decide) with h167 | h167
                · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                    · linarith only [h0, h169, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                      · linarith only [h0, h108, h171, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                        · linarith only [h0, h148, h173, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
                          · linarith only [h1, h175, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h1, h166, h175, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                    · linarith only [h0, h108, h168, h178, h3, hc45, hlam, hphi, ht34, u3ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                      · linarith only [h0, h108, h180, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                        · linarith only [h0, h148, h166, h168, h182, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                          · linarith only [h1, h184, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h166, h168, h184, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h166, h167, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h188 | h188
                · linarith only [h166, h188, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h190 | h190
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                    · linarith only [h0, h191, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
                      · linarith only [h0, h108, h190, h193, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
                        · linarith only [h0, h148, h195, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                          · linarith only [h1, h166, h197, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                            · linarith only [h1, h188, h199, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h205 | h205
                                      · rcases h0emin with h206 | h206 | h206 | h206 | h206
                                        · linarith only [h206, hlam, ht01, u1elo0]
                                        · linarith only [h0, h206, hlam, ht01, u1elo0]
                                        · linarith only [h188, h202, h205, h206, hc23, hlam, ht01, ht12]
                                        · linarith only [h2, h206, hlam, ht01, u1elo0]
                                        · linarith only [h188, h202, h205, h206, hc23, hlam, ht01, ht12]
                                      · linarith only [h1, h166, h205, hc45, hlam, hphi, ht34, u3ehi1]
                                    · linarith only [h1, h166, h2, h201, h202, h204, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                                  · linarith only [h1, h166, h202, h203, hc35, hlam, hphi, u3ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                                  · linarith only [h202, h215, hc34, hlam, hphi, u3ehi4]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h217 | h217
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h218 | h218
                                      · rcases h0emin with h219 | h219 | h219 | h219 | h219
                                        · linarith only [h219, hlam, ht01, u1elo0]
                                        · linarith only [h219, h3, hc23, hlam, ht01, ht12]
                                        · linarith only [h1, h219, hlam, ht01, u1elo0]
                                        · linarith only [h2, h219, hlam, ht01, u1elo0]
                                        · linarith only [h190, h2, h219, hlam, ht01, u1elo0]
                                      · linarith only [h2, h201, h202, h218, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h108, h2, h201, h217, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h190, h197, h2, h201, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h228 | h228
                    · linarith only [h0, h228, h3, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
                      · linarith only [h0, h108, h230, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                        · linarith only [h0, h148, h232, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                          · linarith only [h1, h234, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
                            · linarith only [h1, h236, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                              · linarith only [h166, h190, h2, h238, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h243 | h243
                                      · linarith only [h1, h166, h190, h243, hc34, hlam, hphi, u3ehi1]
                                      · linarith only [h1, h166, h240, h242, h243, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                    · linarith only [h1, h166, h240, h242, hc45, hlam, hphi, ht34, u3ehi1]
                                  · linarith only [h1, h166, h240, h241, hc35, hlam, hphi, u3ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                                  · linarith only [h240, h248, hc34, hlam, hphi, u3ehi4]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                                    · linarith only [h1, h166, h190, h240, h250, hc34, hlam, hphi, u3ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                                      · linarith only [h240, h250, h252, hc34, hlam, hphi, u3ehi2]
                                      · linarith only [h1, h166, h252, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h256 | h256
      · rcases m.htr 0 2 3 (by decide) (by decide) with h257 | h257
        · linarith only [h0, h1, h257, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h259 | h259
          · rcases m.htr 0 2 5 (by decide) (by decide) with h260 | h260
            · rcases m.htr 0 3 4 (by decide) (by decide) with h261 | h261
              · rcases m.htr 0 3 5 (by decide) (by decide) with h262 | h262
                · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                    · linarith only [h257, h259, h264, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                      · linarith only [h0, h1, h266, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h259, h266, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                    · linarith only [h257, h259, h269, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
                      · linarith only [h0, h1, h271, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h259, h271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h261, h262, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h256, h261, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h276 | h276
              · rcases m.htr 0 3 5 (by decide) (by decide) with h277 | h277
                · rcases m.htr 0 4 5 (by decide) (by decide) with h278 | h278
                  · linarith only [h259, h260, h278, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h280 | h280
                    · linarith only [h0, h1, h280, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h282 | h282
                      · linarith only [h0, h1, h282, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h259, h282, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h276, h277, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1, h259, h276, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h287 | h287
            · rcases m.htr 0 3 4 (by decide) (by decide) with h288 | h288
              · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
                · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                    · linarith only [h0, h1, h291, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                      · linarith only [h0, h1, h259, h293, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h295 | h295
                        · linarith only [h1, h256, h293, h295, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h259, h287, h295, hc12, hc24, hlam, hphi]
                  · linarith only [h259, h287, h290, hlam]
                · linarith only [h288, h289, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h256, h288, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h301 | h301
              · rcases m.htr 0 3 5 (by decide) (by decide) with h302 | h302
                · rcases m.htr 0 4 5 (by decide) (by decide) with h303 | h303
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h304 | h304
                    · linarith only [h0, h1, h257, h304, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h306 | h306
                      · linarith only [h0, h1, h259, h306, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h308 | h308
                        · linarith only [h0, h287, h308, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h310 | h310
                          · linarith only [h1, h256, h310, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                          · linarith only [h1, h256, h301, h306, h310, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
                    · linarith only [h0, h313, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
                      · linarith only [h0, h1, h259, h315, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                        · linarith only [h0, h1, h287, h303, h317, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                          · linarith only [h1, h256, h319, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                          · linarith only [h1, h256, h315, h319, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h301, h302, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h256, h301, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h324 | h324
        · linarith only [h0, h1, h324, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h326 | h326
          · linarith only [h0, h256, h326, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h328 | h328
            · rcases m.htr 0 3 4 (by decide) (by decide) with h329 | h329
              · rcases m.htr 0 3 5 (by decide) (by decide) with h330 | h330
                · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                    · linarith only [h324, h328, h332, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
                      · linarith only [h0, h1, h326, h328, h330, h334, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h336 | h336
                        · linarith only [h0, h1, h336, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h0, h1, h328, h336, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h0, h256, h328, h331, hlam]
                · linarith only [h329, h330, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h341 | h341
                · linarith only [h329, h341, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h1, h328, h341, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h344 | h344
              · rcases m.htr 0 3 5 (by decide) (by decide) with h345 | h345
                · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                    · linarith only [h0, h1, h324, h347, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h349 | h349
                      · linarith only [h0, h256, h326, h349, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h351 | h351
                        · linarith only [h0, h256, h351, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h354 | h354
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h355 | h355
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h356 | h356
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h357 | h357
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h358 | h358
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                                      · rcases h0emin with h360 | h360 | h360 | h360 | h360
                                        · linarith only [h256, h353, h360, hlam, ht01, u1elo2]
                                        · linarith only [h0, h256, h353, h360, hlam, ht01, u1elo2]
                                        · linarith only [h1, h360, hlam, ht01, u1elo2]
                                        · linarith only [h256, h353, h360, hlam, ht01, u1elo2]
                                        · linarith only [h1, h345, h360, hlam, ht01, u1elo2]
                                      · linarith only [h256, h346, h353, h359, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                                    · linarith only [h0, h256, h349, h355, h358, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                                  · linarith only [h0, h256, h347, h353, h357, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h256, h347, h353, h356, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h256, h346, h355, hlam]
                            · linarith only [h1, h345, h354, hlam]
                          · linarith only [h1, h344, h353, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                    · linarith only [h0, h256, h373, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h375 | h375
                      · linarith only [h0, h1, h375, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                        · linarith only [h0, h1, h328, h377, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h379 | h379
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h380 | h380
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h381 | h381
                              · linarith only [h256, h346, h379, h381, hc01, hlam, hphi, u1elo2]
                              · linarith only [h0, h256, h381, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h1, h345, h380, hlam]
                          · linarith only [h1, h345, h379, hc34, hlam, hphi, u3ehi4]
                · linarith only [h344, h345, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h387 | h387
                · linarith only [h344, h387, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h389 | h389
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
                    · linarith only [h0, h1, h390, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h392 | h392
                      · linarith only [h0, h1, h392, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h394 | h394
                        · linarith only [h0, h1, h328, h394, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h396 | h396
                          · linarith only [h1, h344, h396, hc01, hlam, hphi, u1elo2]
                          · linarith only [h0, h1, h396, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h399 | h399
                    · linarith only [h0, h1, h399, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h401 | h401
                      · linarith only [h0, h1, h401, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h403 | h403
                        · linarith only [h0, h1, h328, h389, h403, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
                          · linarith only [h1, h344, h405, hc01, hlam, hphi, u1elo2]
                          · linarith only [h0, h1, h405, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h408 | h408
    · linarith only [h0, h408, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h410 | h410
      · rcases m.htr 0 2 3 (by decide) (by decide) with h411 | h411
        · rcases m.htr 0 2 4 (by decide) (by decide) with h412 | h412
          · rcases m.htr 0 2 5 (by decide) (by decide) with h413 | h413
            · rcases m.htr 0 3 4 (by decide) (by decide) with h414 | h414
              · rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
                · rcases m.htr 0 4 5 (by decide) (by decide) with h416 | h416
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h419 | h419
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h420 | h420
                          · linarith only [h408, h410, h417, h420, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · linarith only [h408, h410, h411, h414, h420, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h410, h413, h416, h419, hlam]
                      · linarith only [h408, h410, h412, h416, h417, h418, hc02, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h411, h417, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h427 | h427
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h428 | h428
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h429 | h429
                          · linarith only [h408, h410, h429, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                          · linarith only [h408, h414, h429, hlam]
                        · linarith only [h0, h410, h413, h428, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h412, h427, hlam]
                    · linarith only [h0, h411, h426, hlam]
                · linarith only [h414, h415, hc35, hlam, hphi, u3ehi3]
              · linarith only [h408, h410, h414, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h437 | h437
              · rcases m.htr 0 3 5 (by decide) (by decide) with h438 | h438
                · linarith only [h411, h413, h438, hlam]
                · linarith only [h437, h438, hc35, hlam, hphi, u3ehi3]
              · linarith only [h408, h410, h437, hlam]
          · linarith only [h0, h410, h411, h412, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h443 | h443
          · rcases m.htr 0 2 5 (by decide) (by decide) with h444 | h444
            · rcases m.htr 0 3 4 (by decide) (by decide) with h445 | h445
              · rcases m.htr 0 3 5 (by decide) (by decide) with h446 | h446
                · rcases m.htr 0 4 5 (by decide) (by decide) with h447 | h447
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h448 | h448
                    · linarith only [h411, h443, h448, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h450 | h450
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h451 | h451
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
                          · linarith only [h0, h410, h448, h452, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h408, h446, h452, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h0, h410, h444, h446, h447, h451, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h0, h443, h450, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
                    · linarith only [h0, h411, h457, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h459 | h459
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h460 | h460
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h461 | h461
                          · linarith only [h0, h410, h461, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · linarith only [h0, h410, h445, h457, h461, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h410, h444, h445, h460, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h443, h459, hlam]
                · linarith only [h445, h446, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h410, h411, h445, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h468 | h468
              · rcases m.htr 0 3 5 (by decide) (by decide) with h469 | h469
                · rcases m.htr 0 4 5 (by decide) (by decide) with h470 | h470
                  · linarith only [h0, h410, h444, h470, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h472 | h472
                    · linarith only [h0, h411, h472, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h474 | h474
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h475 | h475
                        · linarith only [h0, h410, h444, h468, h472, h475, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h477 | h477
                          · linarith only [h0, h410, h472, h477, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h410, h468, h472, h477, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h410, h443, h468, h474, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h468, h469, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h410, h411, h468, hlam]
          · linarith only [h0, h410, h443, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h484 | h484
        · rcases m.htr 0 2 4 (by decide) (by decide) with h485 | h485
          · rcases m.htr 0 2 5 (by decide) (by decide) with h486 | h486
            · rcases m.htr 0 3 4 (by decide) (by decide) with h487 | h487
              · rcases m.htr 0 3 5 (by decide) (by decide) with h488 | h488
                · rcases m.htr 0 4 5 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h494 | h494
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h495 | h495
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h496 | h496
                                · linarith only [h0, h484, h496, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                                · linarith only [h408, h487, h490, h496, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                              · linarith only [h410, h489, h495, hlam]
                            · linarith only [h408, h488, h494, hlam]
                          · linarith only [h408, h487, h493, hlam]
                        · linarith only [h0, h486, h492, hlam]
                      · linarith only [h0, h485, h491, hlam]
                    · linarith only [h0, h484, h490, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h505 | h505
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h506 | h506
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h507 | h507
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h509 | h509
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h510 | h510
                              · linarith only [h410, h489, h510, hc01, hlam, hphi, u1elo3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h512 | h512
                                · linarith only [h0, h484, h512, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                                · linarith only [h408, h487, h512, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                            · linarith only [h0, h484, h488, h509, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
                          · linarith only [h408, h487, h508, hlam]
                        · linarith only [h0, h486, h507, hlam]
                      · linarith only [h0, h485, h506, hlam]
                    · linarith only [h0, h484, h505, hlam]
                · linarith only [h487, h488, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h521 | h521
                · linarith only [h487, h521, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h523 | h523
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h524 | h524
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h525 | h525
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h526 | h526
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h527 | h527
                          · linarith only [h487, h527, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h529 | h529
                            · linarith only [h527, h529, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h531 | h531
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h532 | h532
                                · linarith only [h408, h527, h532, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h534 | h534
                                  · linarith only [h0, h408, h485, h529, h532, h534, hc01, hlam, hphi, u1elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h536 | h536
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h537 | h537
                                      · rcases h0emin with h538 | h538 | h538 | h538 | h538
                                        · linarith only [h408, h538, hlam, ht01, u1elo2]
                                        · linarith only [h0, h538, hlam, ht01, u1elo1]
                                        · linarith only [h408, h538, hlam, ht01, u1elo2]
                                        · linarith only [h0, h485, h538, hlam, ht01, u1elo1]
                                        · linarith only [h0, h485, h523, h538, hlam, ht01, u1elo1]
                                      · linarith only [h0, h485, h536, h537, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                    · linarith only [h0, h485, h523, h532, h536, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                              · linarith only [h410, h523, h531, hlam]
                        · linarith only [h0, h486, h526, hlam]
                      · linarith only [h0, h485, h525, hlam]
                    · linarith only [h0, h484, h524, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h551 | h551
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h552 | h552
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h553 | h553
                          · linarith only [h487, h553, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h555 | h555
                            · linarith only [h553, h555, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h557 | h557
                              · linarith only [h410, h523, h557, hc01, hlam, hphi, u1elo3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h559 | h559
                                · linarith only [h408, h553, h559, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h561 | h561
                                  · linarith only [h0, h408, h485, h555, h559, h561, hc01, hlam, hphi, u1elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h563 | h563
                                    · linarith only [h0, h410, h485, h557, h563, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h565 | h565
                                      · linarith only [h408, h553, h557, h565, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · linarith only [h487, h565, hc45, hlam, hphi, ht34, u3ehi0]
                        · linarith only [h0, h486, h552, hlam]
                      · linarith only [h0, h410, h485, h551, hc01, hlam, hphi, u1elo3]
                    · linarith only [h0, h484, h487, h550, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h571 | h571
              · rcases m.htr 0 3 5 (by decide) (by decide) with h572 | h572
                · linarith only [h484, h486, h572, hlam]
                · linarith only [h571, h572, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h575 | h575
                · linarith only [h571, h575, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h577 | h577
                  · linarith only [h485, h486, h577, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h579 | h579
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h580 | h580
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h581 | h581
                        · linarith only [h484, h486, h581, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h583 | h583
                          · linarith only [h571, h583, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h585 | h585
                            · linarith only [h484, h486, h575, h583, h585, hc34, hlam, hphi, u3ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h587 | h587
                              · linarith only [h410, h577, h580, h581, h587, hc01, hc25, hlam, hphi, ht12]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h589 | h589
                                · linarith only [h0, h484, h581, h589, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h591 | h591
                                  · linarith only [h0, h485, h581, h585, h589, h591, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h0, h485, h581, h589, h591, hc35, hlam, hphi, u3ehi2]
                      · linarith only [h0, h485, h580, hlam]
                    · linarith only [h0, h408, h484, h579, hc01, hlam, hphi, u1elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h596 | h596
            · rcases m.htr 0 3 4 (by decide) (by decide) with h597 | h597
              · linarith only [h484, h485, h597, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h599 | h599
                · linarith only [h597, h599, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h601 | h601
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h602 | h602
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h603 | h603
                      · linarith only [h485, h596, h599, h603, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h605 | h605
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h606 | h606
                          · linarith only [h484, h485, h597, h602, h603, h606, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h608 | h608
                            · linarith only [h484, h599, h606, h608, hc34, hlam, hphi, u3ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h610 | h610
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h611 | h611
                                · linarith only [h484, h606, h611, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · linarith only [h0, h484, h603, h611, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h410, h484, h485, h610, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h0, h596, h605, hlam]
                    · linarith only [h0, h484, h602, hlam]
                  · linarith only [h484, h485, h601, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h618 | h618
              · linarith only [h484, h485, h618, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h620 | h620
                · linarith only [h618, h620, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h622 | h622
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h623 | h623
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h624 | h624
                      · linarith only [h484, h485, h624, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h626 | h626
                        · linarith only [h484, h596, h624, h626, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h628 | h628
                          · linarith only [h484, h596, h618, h622, h628, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h630 | h630
                            · linarith only [h484, h596, h620, h628, h630, hc34, hlam, hphi, u3ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h632 | h632
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h633 | h633
                                · linarith only [h484, h628, h633, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · linarith only [h484, h485, h633, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h410, h622, h632, hlam]
                    · linarith only [h0, h484, h623, hlam]
                  · linarith only [h484, h485, h622, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h639 | h639
          · rcases m.htr 0 2 5 (by decide) (by decide) with h640 | h640
            · rcases m.htr 0 3 4 (by decide) (by decide) with h641 | h641
              · rcases m.htr 0 3 5 (by decide) (by decide) with h642 | h642
                · rcases m.htr 0 4 5 (by decide) (by decide) with h643 | h643
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h644 | h644
                    · linarith only [h484, h639, h644, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h646 | h646
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h647 | h647
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h648 | h648
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h649 | h649
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h650 | h650
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h651 | h651
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h652 | h652
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h653 | h653
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h654 | h654
                                      · rcases h0emin with h655 | h655 | h655 | h655 | h655
                                        · linarith only [h655, hlam, ht01, u1elo0]
                                        · linarith only [h0, h655, hlam, ht01, u1elo1]
                                        · linarith only [h408, h655, hlam, ht01, u1elo2]
                                        · linarith only [h410, h655, hlam, ht01, u1elo3]
                                        · linarith only [h410, h643, h655, hlam, ht01, u1elo3]
                                      · linarith only [h0, h639, h643, h644, h654, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                    · linarith only [h0, h639, h643, h644, h651, h653, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h410, h644, h646, h652, hc01, hc35, hlam, hphi, ht12, ht23]
                                · linarith only [h0, h639, h642, h643, h644, h651, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h0, h410, h639, h643, h650, hc01, hlam, hphi, u1elo1]
                            · linarith only [h408, h642, h649, hlam]
                          · linarith only [h408, h641, h648, hlam]
                        · linarith only [h0, h640, h647, hlam]
                      · linarith only [h0, h639, h646, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h670 | h670
                    · linarith only [h484, h639, h670, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h672 | h672
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h673 | h673
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h674 | h674
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h675 | h675
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h676 | h676
                              · linarith only [h641, h643, h676, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h678 | h678
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h679 | h679
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                                    · linarith only [h0, h639, h670, h676, h680, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h682 | h682
                                      · linarith only [h410, h676, h682, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · rcases h0emin with h684 | h684 | h684 | h684 | h684
                                        · linarith only [h410, h684, hlam, ht01, u1elo3]
                                        · linarith only [h0, h670, h684, hc23, hlam, ht01, ht12]
                                        · linarith only [h408, h684, hlam, ht01, u1elo2]
                                        · linarith only [h410, h684, hlam, ht01, u1elo3]
                                        · linarith only [h0, h640, h670, h684, hc23, hlam, ht01, ht12]
                                  · linarith only [h0, h670, h679, hc01, hc35, hlam, hphi, ht12, ht23]
                                · linarith only [h0, h640, h641, h643, h670, h678, hlam]
                            · linarith only [h408, h642, h675, hlam]
                          · linarith only [h0, h408, h640, h641, h642, h643, h674, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                        · linarith only [h0, h640, h673, hlam]
                      · linarith only [h0, h639, h672, hlam]
                · linarith only [h641, h642, hc35, hlam, hphi, u3ehi3]
              · linarith only [h484, h639, h641, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h698 | h698
              · rcases m.htr 0 3 5 (by decide) (by decide) with h699 | h699
                · rcases m.htr 0 4 5 (by decide) (by decide) with h700 | h700
                  · linarith only [h639, h640, h700, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h702 | h702
                    · linarith only [h484, h639, h702, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h704 | h704
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h705 | h705
                        · linarith only [h639, h640, h698, h702, h705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h707 | h707
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h708 | h708
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h709 | h709
                              · linarith only [h698, h700, h709, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h711 | h711
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h712 | h712
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h713 | h713
                                    · linarith only [h410, h639, h709, h713, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                    · linarith only [h0, h639, h705, h711, h713, hc45, hlam, hphi, ht34, u3ehi3]
                                  · linarith only [h408, h699, h712, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                                · linarith only [h0, h702, h711, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h408, h699, h708, hlam]
                          · linarith only [h0, h408, h639, h698, h699, h707, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                      · linarith only [h0, h639, h704, hlam]
                · linarith only [h698, h699, hc35, hlam, hphi, u3ehi3]
              · linarith only [h484, h639, h698, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h723 | h723
            · rcases m.htr 0 3 4 (by decide) (by decide) with h724 | h724
              · rcases m.htr 0 3 5 (by decide) (by decide) with h725 | h725
                · rcases m.htr 0 4 5 (by decide) (by decide) with h726 | h726
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h727 | h727
                    · linarith only [h484, h723, h727, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h729 | h729
                      · linarith only [h639, h723, h725, h727, h729, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h731 | h731
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h732 | h732
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h733 | h733
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h734 | h734
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h735 | h735
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h736 | h736
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h737 | h737
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h738 | h738
                                      · rcases h0emin with h739 | h739 | h739 | h739 | h739
                                        · linarith only [h0, h729, h732, h739, hlam, ht01, u1elo2]
                                        · linarith only [h0, h729, h732, h739, hlam, ht01, u1elo2]
                                        · linarith only [h408, h739, hlam, ht01, u1elo2]
                                        · linarith only [h410, h732, h739, hlam, ht01, u1elo2]
                                        · linarith only [h0, h723, h729, h732, h739, hlam, ht01, u1elo2]
                                      · linarith only [h410, h726, h732, h738, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                                    · linarith only [h0, h410, h726, h729, h732, h737, hc01, hlam, hphi, u1elo2]
                                  · linarith only [h484, h724, h736, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h0, h723, h724, h725, h727, h735, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h410, h726, h734, hlam]
                            · linarith only [h0, h408, h723, h724, h725, h727, h733, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h408, h725, h732, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h0, h723, h731, hlam]
                  · linarith only [h639, h723, h726, hlam]
                · linarith only [h724, h725, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h755 | h755
                · linarith only [h724, h755, hc34, hlam, hphi, u3ehi4]
                · linarith only [h484, h723, h755, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h758 | h758
              · rcases m.htr 0 3 5 (by decide) (by decide) with h759 | h759
                · rcases m.htr 0 4 5 (by decide) (by decide) with h760 | h760
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
                    · linarith only [h0, h484, h761, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h763 | h763
                      · linarith only [h0, h639, h761, h763, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h765 | h765
                        · linarith only [h0, h723, h761, h765, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h767 | h767
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h768 | h768
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h769 | h769
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h770 | h770
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h772 | h772
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h773 | h773
                                      · rcases h0emin with h774 | h774 | h774 | h774 | h774
                                        · linarith only [h774, hlam, ht01, u1elo0]
                                        · linarith only [h0, h765, h767, h769, h774, hlam, ht01, u1elo2]
                                        · linarith only [h408, h774, hlam, ht01, u1elo2]
                                        · linarith only [h408, h758, h774, hlam, ht01, u1elo2]
                                        · linarith only [h408, h759, h774, hlam, ht01, u1elo2]
                                      · linarith only [h408, h758, h760, h773, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                                    · linarith only [h408, h639, h758, h760, h772, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                                  · linarith only [h484, h758, h771, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h0, h758, h761, h770, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · linarith only [h410, h760, h769, hlam]
                            · linarith only [h408, h410, h759, h760, h768, hc01, hlam, hphi, u1elo3]
                          · linarith only [h408, h759, h767, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h787 | h787
                    · linarith only [h0, h484, h787, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h789 | h789
                      · linarith only [h0, h639, h789, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h791 | h791
                        · linarith only [h0, h723, h791, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h793 | h793
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h794 | h794
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h795 | h795
                              · linarith only [h410, h760, h793, h795, hc01, hlam, hphi, u1elo2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h797 | h797
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h798 | h798
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h799 | h799
                                    · linarith only [h410, h795, h799, hc01, hc24, hlam, hphi, ht12]
                                    · linarith only [h0, h789, h799, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h408, h759, h798, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                                · linarith only [h0, h787, h797, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h408, h759, h794, hlam]
                          · linarith only [h408, h758, h793, hlam]
                · linarith only [h758, h759, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h807 | h807
                · linarith only [h758, h807, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h809 | h809
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h810 | h810
                    · linarith only [h0, h484, h810, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h812 | h812
                      · linarith only [h0, h639, h810, h812, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h814 | h814
                        · linarith only [h0, h723, h810, h814, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h816 | h816
                          · linarith only [h758, h816, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h818 | h818
                            · linarith only [h816, h818, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h820 | h820
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h821 | h821
                                · linarith only [h0, h810, h816, h821, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h810, h821, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h410, h809, h820, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
                    · linarith only [h0, h484, h825, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h827 | h827
                      · linarith only [h0, h639, h827, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h829 | h829
                        · linarith only [h0, h723, h829, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h831 | h831
                          · linarith only [h758, h831, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h833 | h833
                            · linarith only [h831, h833, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h835 | h835
                              · linarith only [h410, h809, h835, hc01, hlam, hphi, u1elo3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h837 | h837
                                · linarith only [h408, h831, h837, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h825, h837, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
