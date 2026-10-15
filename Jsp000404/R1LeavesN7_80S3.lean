import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_R_L_R_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h10, h16, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · linarith only [h0, h10, h13, h16, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                                  · linarith only [h0, h10, h19, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · linarith only [h0, h10, h13, h19, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h13, h14, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                              · linarith only [h0, h13, h23, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                                  · linarith only [h13, h26, hc23, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                                    · linarith only [h23, h28, hc23, hlam, hphi, ht12, u1ehi2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                                      · linarith only [h0, h11, h30, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h2, h25, h30, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                                  · linarith only [h0, h10, h13, h25, h33, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                                    · linarith only [h0, h10, h13, h23, h25, h35, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                                      · linarith only [h13, h25, h37, hc24, hlam, hphi, ht12, u1ehi2]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                                        · linarith only [h13, h25, h39, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                        · linarith only [h0, h13, h39, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                          · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                        · linarith only [h0, h10, h4, h44, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h10, h4, h46, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                                        · linarith only [h1, h48, h54, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                        · linarith only [h2, h50, h54, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                      · linarith only [h44, h50, h53, hlam]
                                    · linarith only [h10, h49, h52, hlam]
                                  · linarith only [h0, h10, h4, h49, h51, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                                      · linarith only [h44, h50, h60, h62, hc23, hlam, hphi, ht12, u1ehi1]
                                      · linarith only [h0, h4, h44, h62, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                    · linarith only [h0, h10, h4, h61, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                  · linarith only [h10, h48, h60, hc13, hlam, hphi, u1ehi1]
                              · linarith only [h0, h4, h48, h49, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                              · linarith only [h0, h4, h48, h68, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                                  · linarith only [h0, h4, h48, h71, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                  · linarith only [h0, h10, h4, h7, h71, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                                  · linarith only [h10, h48, h74, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h0, h10, h4, h7, h74, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                                · linarith only [h2, h82, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                                  · linarith only [h0, h77, h84, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · linarith only [h1, h80, h84, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h4, h8, h80, h81, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h7, h80, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · linarith only [h0, h6, h77, h79, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h77, h78, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                        · linarith only [h77, h91, hc23, hlam, hphi, u2ehi3]
                        · linarith only [h5, h9, h91, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h94 | h94
                    · linarith only [h7, h8, h94, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h96 | h96
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                              · linarith only [h1, h100, h8, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                                · linarith only [h102, h2, h94, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                                  · linarith only [h0, h104, h96, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · linarith only [h1, h104, h8, h99, hc23, hc35, hlam, hphi]
                            · linarith only [h7, h8, h99, hc13, hc35, hlam, hphi]
                          · linarith only [h0, h6, h96, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h96, h97, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h4, h8, h96, hc35, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h112 | h112
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                            · linarith only [h1, h116, h7, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                                  · linarith only [h1, h113, h118, h120, h7, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                                    · linarith only [h0, h114, h120, h122, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · linarith only [h1, h118, h122, h7, hc23, hc34, hlam, hphi]
                                · linarith only [h112, h119, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h111, h118, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                          · linarith only [h111, h115, h6, h7, hc34, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h113, h114, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h113, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h111, h112, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h131 | h131
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                            · linarith only [h1, h135, h7, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                              · linarith only [h1, h111, h137, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                                  · linarith only [h1, h140, h7, hc23, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                                    · linarith only [h0, h111, h133, h140, h142, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                                      · linarith only [h0, h133, h144, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · linarith only [h131, h144, h7, hc34, hlam, hphi, ht23, u2ehi3]
                                · linarith only [h131, h139, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h0, h132, h134, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h132, h133, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h132, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                            · linarith only [h1, h131, h154, h7, hc45, hlam, hphi, u4ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
                              · linarith only [h1, h111, h156, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                                · linarith only [h1, h131, h158, h7, hc14, hlam, hphi, u1ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                                  · linarith only [h1, h151, h160, h7, hc12, hlam, hphi, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                                    · linarith only [h1, h111, h151, h162, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                                      · linarith only [h0, h1, h131, h152, h164, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
                                        · linarith only [h1, h131, h166, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                        · linarith only [h1, h166, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · linarith only [h0, h151, h153, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h151, h152, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h151, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h174 | h174
            · linarith only [h174, h4, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h176 | h176
              · linarith only [h176, h4, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
                · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h180 | h180
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
                      · linarith only [h0, h181, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h183 | h183
                        · linarith only [h0, h174, h183, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                          · linarith only [h0, h176, h185, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h188 | h188
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h191 | h191
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                                        · linarith only [h1, h187, h193, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                        · linarith only [h189, h193, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                      · linarith only [h1, h187, h189, h192, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                    · linarith only [h0, h1, h174, h188, h190, h191, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                  · linarith only [h0, h190, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h178, h180, h189, h4, hc23, hlam, hphi, ht12, u1ehi3]
                              · linarith only [h179, h187, h188, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                            · linarith only [h178, h181, h187, h4, hc23, hlam, hphi, u2ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                      · linarith only [h0, h174, h180, h202, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
                        · linarith only [h0, h174, h204, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                          · linarith only [h0, h176, h206, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h209 | h209
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
                                · linarith only [h0, h174, h180, h210, hc14, hlam, hphi, u1ehi1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                                      · linarith only [h0, h174, h180, h212, h214, hc23, hlam, hphi, ht12, u1ehi1]
                                      · linarith only [h0, h174, h214, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                    · linarith only [h1, h209, h213, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · linarith only [h0, h212, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h179, h208, h209, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h178, h208, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
                    · linarith only [h178, h179, h221, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
                      · linarith only [h0, h174, h223, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                        · linarith only [h0, h174, h225, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                          · linarith only [h0, h176, h227, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                              · linarith only [h1, h179, h230, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
                                · linarith only [h2, h221, h232, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
                                    · linarith only [h1, h179, h229, h235, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                    · linarith only [h0, h235, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                  · linarith only [h0, h1, h229, h234, h4, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h178, h179, h229, hc13, hc35, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h240 | h240
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                      · linarith only [h0, h174, h242, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                        · linarith only [h0, h244, h4, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h246 | h246
                          · linarith only [h0, h176, h178, h240, h246, hc34, hlam, hphi, ht23, u2ehi4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
                            · linarith only [h1, h178, h248, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h250 | h250
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h251 | h251
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h252 | h252
                                  · linarith only [h176, h178, h240, h252, hc23, hlam, hphi, u2ehi0]
                                  · linarith only [h0, h252, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h174, h241, h251, hc24, hlam, hphi, ht12, u1ehi3]
                              · linarith only [h178, h240, h250, hc13, hc34, hlam, hphi]
                    · linarith only [h178, h240, h241, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h258 | h258
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h259 | h259
                      · linarith only [h0, h259, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h261 | h261
                        · linarith only [h0, h261, h4, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
                          · linarith only [h1, h240, h259, h263, hc35, hlam, hphi, ht23, u2ehi4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h265 | h265
                            · linarith only [h1, h178, h240, h258, h265, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                              · linarith only [h1, h240, h267, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                                  · linarith only [h178, h270, h4, hc23, hlam, hphi, u2ehi0]
                                  · linarith only [h0, h270, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h178, h258, h269, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
                      · linarith only [h0, h274, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
                        · linarith only [h0, h276, h4, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h278 | h278
                          · linarith only [h0, h176, h278, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h280 | h280
                            · linarith only [h1, h178, h258, h280, hc45, hlam, hphi, u4ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h282 | h282
                              · linarith only [h1, h240, h282, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                                · linarith only [h0, h178, h258, h284, h4, hc14, hlam, hphi, u1ehi1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h286 | h286
                                  · linarith only [h0, h178, h286, h4, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h0, h286, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h292 | h292
    · linarith only [h0, h292, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h294 | h294
      · linarith only [h0, h294, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h296 | h296
        · linarith only [h0, h296, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h298 | h298
          · rcases m.htr 0 2 4 (by decide) (by decide) with h299 | h299
            · rcases m.htr 0 2 5 (by decide) (by decide) with h300 | h300
              · rcases m.htr 0 3 4 (by decide) (by decide) with h301 | h301
                · rcases m.htr 0 3 5 (by decide) (by decide) with h302 | h302
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h303 | h303
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h304 | h304
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h305 | h305
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h306 | h306
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h308 | h308
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h311 | h311
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h313 | h313
                                        · linarith only [h298, h310, h313, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                        · linarith only [h0, h299, h312, h313, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h316 | h316
                                        · linarith only [h312, h316, hc34, hlam, hphi, ht23, u2ehi3]
                                        · rcases h5bigk with h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [hlam, p318_0]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h296, hlam, p318_1]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            rcases p318_3 (m.d 0 5) (by simp) with h321 | h321
                                            · rcases p318_3 (m.d 1 5) (by simp) with h322 | h322
                                              · rcases p318_3 (m.d 2 5) (by simp) with h323 | h323
                                                · linarith only [h300, h323, hlam]
                                                · rcases p318_3 (m.d 3 5) (by simp) with h325 | h325
                                                  · linarith only [h302, h325, hlam]
                                                  · rcases p318_3 (m.d 4 5) (by simp) with h327 | h327
                                                    · linarith only [h303, h327, hlam]
                                                    · linarith only [h312, h327, hlam]
                                              · linarith only [h306, h322, hlam]
                                            · linarith only [h300, h321, hlam]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            rcases p318_3 (m.d 0 5) (by simp) with h332 | h332
                                            · rcases p318_3 (m.d 1 5) (by simp) with h333 | h333
                                              · rcases p318_3 (m.d 2 5) (by simp) with h334 | h334
                                                · linarith only [h300, h334, hlam]
                                                · linarith only [h311, h334, hlam]
                                              · linarith only [h308, h333, hlam]
                                            · linarith only [h302, h332, hlam]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h296, h304, h307, h309, h312, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p318_1, u2ehi3]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h296, h304, h307, h309, hc12, hlam, hphi, p318_1, u1ehi0]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [hlam, p318_0]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            rcases p318_3 (m.d 0 5) (by simp) with h342 | h342
                                            · linarith only [h296, h342, hlam]
                                            · linarith only [h300, h342, hlam]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            rcases p318_3 (m.d 0 5) (by simp) with h345 | h345
                                            · linarith only [h296, h345, hlam]
                                            · linarith only [h302, h345, hlam]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h304, h307, h309, h312, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p318_1, u2ehi3]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h300, hlam, p318_1]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h306, hlam, p318_1]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [hlam, p318_0]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h0, h300, h316, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p318_1, u4ehi3]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h312, hlam, p318_0]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h302, hlam, p318_1]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h308, hlam, p318_1]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h311, hlam, p318_0]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [hlam, p318_0]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h316, hlam, p318_0]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h303, hlam, p318_1]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h309, hlam, p318_1]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h301, h303, hc03, hlam, hphi, ht0b, ht5b, p318_1, u5ehi2]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [h292, h301, h303, h304, h316, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p318_1, u4ehi3]
                                          · have p318_0 := h318c.1
                                            have p318_1 := h318c.2.1
                                            have p318_2 := h318c.2.2.1
                                            have p318_3 := h318c.2.2.2
                                            linarith only [hlam, p318_0]
                                    · linarith only [h292, h302, h304, h310, h311, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                                    · linarith only [h292, h301, h304, h310, h365, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h367 | h367
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h368 | h368
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
                                            linarith only [h296, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            rcases p369_3 (m.d 0 5) (by simp) with h372 | h372
                                            · rcases p369_3 (m.d 1 5) (by simp) with h373 | h373
                                              · rcases p369_3 (m.d 2 5) (by simp) with h374 | h374
                                                · linarith only [h300, h374, hlam]
                                                · rcases p369_3 (m.d 3 5) (by simp) with h376 | h376
                                                  · linarith only [h302, h376, hlam]
                                                  · linarith only [h365, h376, hlam]
                                              · linarith only [h306, h373, hlam]
                                            · linarith only [h300, h372, hlam]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h296, h304, h307, h309, h365, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p369_1, u2ehi2]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            rcases p369_3 (m.d 0 5) (by simp) with h382 | h382
                                            · rcases p369_3 (m.d 1 5) (by simp) with h383 | h383
                                              · rcases p369_3 (m.d 2 5) (by simp) with h384 | h384
                                                · linarith only [h300, h384, hlam]
                                                · linarith only [h367, h384, hlam]
                                              · linarith only [h309, h383, hlam]
                                            · linarith only [h303, h382, hlam]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h296, h304, h307, h309, hc12, hlam, hphi, p369_1, u1ehi0]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [hlam, p369_0]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            rcases p369_3 (m.d 0 5) (by simp) with h391 | h391
                                            · linarith only [h296, h391, hlam]
                                            · linarith only [h300, h391, hlam]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h304, h307, h309, h365, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p369_1, u2ehi2]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            rcases p369_3 (m.d 0 5) (by simp) with h395 | h395
                                            · linarith only [h296, h395, hlam]
                                            · linarith only [h303, h395, hlam]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h300, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h306, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [hlam, p369_0]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h365, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h0, h300, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p369_1, u4ehi4]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h302, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h308, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [hc35, hlam, hphi, ht23, p369_1, u2ehi4]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [hlam, p369_0]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h292, h301, h304, h368, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p369_1, u4ehi4]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h303, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h309, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h367, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [h368, hlam, p369_1]
                                          · have p369_0 := h369c.1
                                            have p369_1 := h369c.2.1
                                            have p369_2 := h369c.2.2.1
                                            have p369_3 := h369c.2.2.2
                                            linarith only [hlam, p369_0]
                                        · linarith only [h0, h299, h367, h368, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                                        · linarith only [h292, h301, h304, h310, h367, h414, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                        · linarith only [h310, h414, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h292, h301, h303, h304, h309, hc12, hlam, hphi, u1ehi3]
                              · linarith only [h292, h308, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                            · linarith only [h292, h307, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h300, h306, hlam]
                        · linarith only [h0, h300, h305, hc24, hlam, hphi, u2ehi4]
                      · linarith only [h0, h304, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h423 | h423
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h424 | h424
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h426 | h426
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h427 | h427
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h428 | h428
                                · linarith only [h294, h303, h423, h426, h428, hc12, hlam, hphi, u1ehi0]
                                · linarith only [h294, h428, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                              · linarith only [h292, h302, h427, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                            · linarith only [h292, h426, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h298, h425, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h292, h299, h423, h424, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                      · linarith only [h0, h300, h423, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
                    · linarith only [h301, h302, h436, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h438 | h438
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h442 | h442
                              · linarith only [h301, h302, h438, h442, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h292, h442, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                            · linarith only [h292, h301, h441, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                          · linarith only [h0, h300, h440, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                        · linarith only [h0, h299, h436, h439, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h0, h298, h438, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h451 | h451
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                            · linarith only [h301, h449, h454, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h292, h454, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h453, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h0, h299, h452, hlam]
                      · linarith only [h0, h298, h451, hlam]
                    · linarith only [h301, h449, h450, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h461 | h461
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h463 | h463
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h464 | h464
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h465 | h465
                            · linarith only [h292, h301, h465, hc13, hlam, hphi, u1ehi0]
                            · linarith only [h292, h465, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h300, h464, hlam]
                        · linarith only [h0, h299, h463, hlam]
                      · linarith only [h0, h298, h462, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h472 | h472
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h473 | h473
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h474 | h474
                            · linarith only [h292, h301, h474, hc13, hlam, hphi, u1ehi0]
                            · linarith only [h292, h474, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h300, h473, hlam]
                        · linarith only [h0, h299, h472, hlam]
                      · linarith only [h0, h298, h471, hlam]
              · linarith only [h298, h300, hc25, hlam, hphi, u2ehi2]
            · linarith only [h298, h299, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h482 | h482
            · linarith only [h298, h482, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h484 | h484
              · linarith only [h298, h484, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h486 | h486
                · rcases m.htr 0 3 5 (by decide) (by decide) with h487 | h487
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                      · linarith only [h0, h298, h489, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h489, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
                      · linarith only [h0, h298, h492, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h492, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h495 | h495
                    · linarith only [h486, h487, h495, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
                      · linarith only [h0, h298, h497, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h497, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h500 | h500
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h501 | h501
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
                      · linarith only [h0, h298, h502, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h502, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h486, h500, h501, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h506 | h506
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
                      · linarith only [h0, h298, h507, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h507, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
                      · linarith only [h0, h298, h510, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h510, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_11_13_25_L_0_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
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
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h1, h6, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · linarith only [h0, h4, h8, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h12, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
                    · linarith only [h1, h14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h14, h16, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h1, h16, h5, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h19, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h1, h19, h22, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · linarith only [h0, h21, h22, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h25, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                    · linarith only [h1, h27, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h2, h27, h29, h5, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                        · linarith only [h2, h31, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                            · linarith only [h34, h4, h5, hlam]
                            · linarith only [h27, h33, h34, hc35, hlam, hphi, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                            · linarith only [h33, h37, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
                              · linarith only [h27, h31, h33, h39, hc34, hlam, hphi, u3ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                                · linarith only [h27, h31, h41, hc34, hlam, hphi, u3ehi1]
                                · linarith only [h27, h41, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
            · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
              · linarith only [h0, h45, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                  · linarith only [h1, h4, h45, h48, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                    · linarith only [h1, h50, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · linarith only [h45, h47, h50, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                  · linarith only [h0, h4, h53, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                    · linarith only [h1, h55, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                      · linarith only [h2, h55, h57, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi4]
                      · linarith only [h1, h44, h57, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
              · linarith only [h0, h60, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
                · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                  · linarith only [h0, h4, h63, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                    · linarith only [h1, h65, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · linarith only [h60, h62, h65, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
                  · linarith only [h0, h4, h68, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h70 | h70
                    · linarith only [h1, h70, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h72 | h72
                      · linarith only [h2, h70, h72, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                        · linarith only [h2, h74, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                                · linarith only [h70, h74, h79, hc34, hlam, hphi, u3ehi1]
                                · linarith only [h70, h76, h78, h79, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                              · linarith only [h70, h76, h78, hc45, hlam, hphi, ht34, u3ehi1]
                            · linarith only [h70, h76, h77, hc35, hlam, hphi, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                            · linarith only [h76, h84, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h86 | h86
                              · linarith only [h70, h74, h76, h86, hc34, hlam, hphi, u3ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                                · linarith only [h60, h76, h86, h88, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h70, h88, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi1]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h93 | h93
      · rcases m.htr 0 1 5 (by decide) (by decide) with h94 | h94
        · linarith only [h1, h94, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h96 | h96
          · linarith only [h0, h1, h96, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h98 | h98
            · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
              · linarith only [h0, h1, h99, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                · linarith only [h0, h1, h101, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                  · linarith only [h1, h101, h103, h93, h96, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                    · linarith only [h1, h105, h93, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h1, h101, h105, h93, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
              · linarith only [h0, h108, h94, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                · linarith only [h0, h110, h94, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                  · linarith only [h110, h112, h93, h94, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                    · linarith only [h114, h93, h94, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi3]
                    · linarith only [h1, h110, h114, h93, hc12, hc34, hlam, hphi, ht23]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h117 | h117
        · linarith only [h1, h117, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h119 | h119
          · linarith only [h0, h1, h119, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h121 | h121
            · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
              · linarith only [h0, h1, h122, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                · linarith only [h0, h1, h124, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                  · linarith only [h0, h1, h119, h126, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                                · linarith only [h128, h134, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                                · linarith only [h128, h130, h134, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                              · linarith only [h124, h130, h133, hlam]
                            · linarith only [h121, h122, h128, h130, h132, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h0, h117, h122, h128, h130, h131, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h130, h93, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h121, h128, h129, h93, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h121, h128, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
              · linarith only [h0, h1, h143, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                · linarith only [h0, h1, h145, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                  · linarith only [h0, h1, h147, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h150 | h150
                      · linarith only [h121, h150, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                      · linarith only [h0, h149, h150, h93, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h149, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h154 | h154
    · linarith only [h0, h154, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h156 | h156
      · rcases m.htr 0 1 5 (by decide) (by decide) with h157 | h157
        · linarith only [h0, h157, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h159 | h159
          · rcases m.htr 0 3 5 (by decide) (by decide) with h160 | h160
            · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
              · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                · rcases m.htr 1 2 5 (by decide) (by decide) with h163 | h163
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h164 | h164
                    · linarith only [h154, h156, h161, h164, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                    · linarith only [h154, h160, h164, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h154, h159, h160, h161, h163, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h154, h156, h161, h162, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                    · linarith only [h156, h157, h170, h171, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                    · linarith only [h154, h160, h171, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h159, h170, hlam]
                · linarith only [h0, h156, h157, h159, h169, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
              · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                    · linarith only [h154, h156, h176, h179, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                    · linarith only [h154, h156, h179, hlam]
                  · linarith only [h0, h159, h178, hlam]
                · linarith only [h156, h176, h177, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
                · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                    · linarith only [h156, h157, h176, h185, h186, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h156, h157, h176, h185, h186, hlam]
                  · linarith only [h0, h159, h185, hlam]
                · linarith only [h0, h156, h157, h159, h160, h184, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h191 | h191
            · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
              · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
                · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                  · linarith only [h0, h159, h194, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                    · linarith only [h0, h156, h194, h196, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h154, h191, h196, hc34, hlam, hphi, u3ehi4]
                · linarith only [h154, h156, h192, h193, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h200 | h200
                · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                  · linarith only [h0, h159, h192, h201, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
                    · linarith only [h0, h156, h192, h203, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h154, h191, h203, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h156, h200, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h207 | h207
              · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
                · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                  · linarith only [h0, h159, h209, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
                    · linarith only [h0, h156, h209, h211, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h154, h156, h211, hlam]
                · linarith only [h154, h156, h207, h208, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
                · rcases m.htr 1 2 5 (by decide) (by decide) with h216 | h216
                  · linarith only [h0, h159, h207, h216, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h218 | h218
                    · linarith only [h0, h156, h207, h218, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h0, h156, h207, h218, hlam]
                · linarith only [h0, h156, h215, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h222 | h222
        · linarith only [h0, h222, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h224 | h224
          · rcases m.htr 0 3 5 (by decide) (by decide) with h225 | h225
            · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
              · rcases m.htr 1 2 4 (by decide) (by decide) with h227 | h227
                · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                          · linarith only [h226, h232, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · linarith only [h226, h229, h232, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                          · linarith only [h226, h235, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · linarith only [h229, h235, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                      · linarith only [h225, h229, h230, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h154, h225, h229, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h224, h228, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
                    · linarith only [h226, h227, h242, hlam]
                    · linarith only [h154, h225, h242, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h154, h222, h224, h225, h226, h241, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h246 | h246
                · rcases m.htr 1 2 5 (by decide) (by decide) with h247 | h247
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h249 | h249
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h250 | h250
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h252 | h252
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h253 | h253
                              · linarith only [h226, h246, h253, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · linarith only [h250, h251, h253, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi3]
                            · linarith only [h226, h246, h250, h252, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h226, h246, h250, h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                              · linarith only [h156, h250, h260, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h262 | h262
                                · linarith only [h156, h224, h250, h258, h260, h262, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases h5bigk with h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [hlam, p264_0]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h222, hlam, p264_1]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h222, hlam, hphi, ht01, ht0b, ht5b, p264_1, u1elo4, u5ehi2]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h0, h224, h226, h262, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p264_1, u1elo2, u3ehi3]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h0, h156, h224, h226, h250, hc01, hlam, hphi, p264_1, u1elo2]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h226, h247, hlam, hphi, ht01, ht0b, ht5b, p264_1, u1elo2, u5ehi0]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [hlam, p264_0]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h226, h247, h258, h260, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p264_1, u1elo2, u3ehi3]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h226, h247, h262, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p264_1, u1elo2, u3ehi3]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h250, hlam, p264_1]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h224, hlam, p264_1]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h247, hlam, p264_1]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [hlam, p264_0]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h222, h224, h226, h247, h262, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p264_1, u1elo2, u3ehi3]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h260, hlam, p264_1]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h225, hlam, p264_0]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h249, hlam, p264_0]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h259, hlam, p264_0]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [hlam, p264_0]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h262, hlam, p264_1]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h225, h262, hc45, hlam, hphi, ht34, p264_1, u3ehi3]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h222, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p264_1]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h259, h262, hc45, hlam, hphi, ht34, p264_1, u3ehi3]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [h262, hc45, hlam, hphi, ht34, p264_1, u3ehi3]
                                  · have p264_0 := h264c.1
                                    have p264_1 := h264c.2.1
                                    have p264_2 := h264c.2.2.1
                                    have p264_3 := h264c.2.2.2
                                    linarith only [hlam, p264_0]
                            · linarith only [h0, h224, h226, h259, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h0, h224, h226, h258, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h248, h249, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h154, h225, h248, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h224, h247, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h297 | h297
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h299 | h299
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h300 | h300
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h301 | h301
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h302 | h302
                                · linarith only [h296, h302, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                                · linarith only [h298, h302, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi3]
                              · linarith only [h0, h224, h246, h296, h298, h300, h301, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi4]
                            · linarith only [h0, h224, h246, h299, h300, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h0, h224, h226, h299, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h246, h295, h298, hlam]
                      · linarith only [h154, h225, h297, hlam]
                    · linarith only [h154, h225, h296, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h224, h295, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h312 | h312
              · rcases m.htr 1 2 4 (by decide) (by decide) with h313 | h313
                · rcases m.htr 1 2 5 (by decide) (by decide) with h314 | h314
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h315 | h315
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h316 | h316
                      · linarith only [h225, h312, h316, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi0]
                      · linarith only [h315, h316, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h319 | h319
                      · linarith only [h315, h319, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                          · linarith only [h312, h322, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h324 | h324
                            · linarith only [h313, h319, h322, h324, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h326 | h326
                              · linarith only [h313, h326, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                              · linarith only [h313, h321, h322, h326, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h329 | h329
                          · linarith only [h154, h315, h329, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                            · linarith only [h154, h319, h331, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h333 | h333
                              · linarith only [h313, h321, h333, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h335 | h335
                                · linarith only [h154, h315, h321, h335, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h0, h154, h224, h315, h329, h333, h335, hc01, hc45, hlam, hphi, ht34, u1elo1, u3ehi2]
                  · linarith only [h0, h224, h314, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h339 | h339
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
                    · linarith only [h312, h313, h340, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h342 | h342
                      · linarith only [h340, h342, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h344 | h344
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h345 | h345
                          · linarith only [h154, h340, h345, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h312, h313, h345, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h312, h313, h344, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h224, h339, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                · rcases m.htr 1 2 5 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
                      · linarith only [h225, h353, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                      · linarith only [h352, h353, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h312, h350, h352, hlam]
                  · linarith only [h0, h224, h351, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h358 | h358
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
                      · linarith only [h225, h360, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                      · linarith only [h359, h360, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h363 | h363
                      · linarith only [h359, h363, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h312, h358, h363, hlam]
                  · linarith only [h0, h224, h358, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h367 | h367
            · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
              · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
                · rcases m.htr 1 2 5 (by decide) (by decide) with h370 | h370
                  · linarith only [h0, h224, h370, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
                      · linarith only [h368, h370, h373, hlam]
                      · linarith only [h154, h367, h373, hlam]
                    · linarith only [h154, h367, h372, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                  · linarith only [h0, h224, h369, h377, hc01, hlam, hphi, u1elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h379 | h379
                    · linarith only [h368, h369, h379, hlam]
                    · linarith only [h154, h367, h379, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h382 | h382
                · rcases m.htr 1 2 5 (by decide) (by decide) with h383 | h383
                  · linarith only [h0, h224, h383, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h386 | h386
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h387 | h387
                        · linarith only [h382, h383, h387, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h390 | h390
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h391 | h391
                              · linarith only [h382, h383, h386, h387, h391, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                              · linarith only [h382, h383, h389, h391, hc45, hlam, hphi, ht34, u3ehi3]
                            · linarith only [h154, h367, h390, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                          · linarith only [h0, h368, h389, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h154, h367, h386, hlam]
                    · linarith only [h154, h367, h385, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
                  · linarith only [h0, h224, h398, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h400 | h400
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h401 | h401
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h402 | h402
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h403 | h403
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h404 | h404
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h405 | h405
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h406 | h406
                                · linarith only [h400, h406, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                                · linarith only [h400, h402, h406, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                              · linarith only [h382, h400, h402, h405, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · linarith only [h0, h154, h367, h382, h403, h404, hc01, hlam, hphi, u1elo2]
                          · linarith only [h0, h368, h403, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h414 | h414
                              · linarith only [h156, h402, h412, h414, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h382, h414, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h154, h367, h413, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                          · linarith only [h0, h368, h400, h412, hc01, hlam, hphi, u1elo2]
                      · linarith only [h154, h367, h401, hlam]
                    · linarith only [h154, h367, h400, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
              · rcases m.htr 1 2 4 (by decide) (by decide) with h422 | h422
                · rcases m.htr 1 2 5 (by decide) (by decide) with h423 | h423
                  · linarith only [h0, h224, h423, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h425 | h425
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h426 | h426
                      · linarith only [h367, h426, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                      · linarith only [h425, h426, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h429 | h429
                      · linarith only [h425, h429, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h431 | h431
                        · linarith only [h422, h423, h431, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h433 | h433
                          · linarith only [h154, h425, h433, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
                            · linarith only [h154, h422, h423, h429, h433, h435, hc01, hc25, hlam, hphi, ht12]
                            · linarith only [h422, h423, h433, h435, hc35, hlam, hphi, u3ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h438 | h438
                  · linarith only [h0, h224, h438, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h440 | h440
                    · linarith only [h421, h422, h440, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h442 | h442
                      · linarith only [h440, h442, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h444 | h444
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h445 | h445
                          · linarith only [h154, h440, h445, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h421, h422, h445, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h421, h422, h444, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h449 | h449
                · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
                  · linarith only [h0, h224, h450, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h453 | h453
                      · linarith only [h367, h453, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                      · linarith only [h452, h453, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h421, h449, h452, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h457 | h457
                  · linarith only [h0, h224, h457, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h460 | h460
                      · linarith only [h367, h460, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                      · linarith only [h459, h460, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h463 | h463
                      · linarith only [h459, h463, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                          · linarith only [h154, h459, h466, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h421, h466, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h469 | h469
                          · linarith only [h0, h421, h459, h469, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h421, h469, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
