import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h10, h15, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h10, h13, h15, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                              · linarith only [h0, h10, h18, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h10, h13, h18, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                              · linarith only [h0, h13, h22, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                                · linarith only [h0, h10, h13, h24, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                                  · linarith only [h0, h11, h26, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h2, h21, h26, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                              · linarith only [h0, h10, h13, h21, h29, h4, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                                · linarith only [h0, h10, h31, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                                  · linarith only [h10, h13, h21, h33, hc24, hlam, hphi, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                                    · linarith only [h10, h13, h21, h35, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h0, h10, h13, h35, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                      · linarith only [h10, h40, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                        · linarith only [h0, h10, h4, h42, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                                    · linarith only [h1, h44, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h2, h45, h49, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h40, h45, h48, hlam]
                                · linarith only [h0, h4, h40, h45, h46, h47, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h10, h46, hc34, hlam, hphi, ht23, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                                  · linarith only [h40, h45, h55, h57, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h4, h40, h57, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h10, h4, h56, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h10, h44, h55, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                              · linarith only [h0, h4, h44, h63, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · linarith only [h10, h63, hc34, hlam, hphi, ht23, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                              · linarith only [h0, h10, h4, h44, h66, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h10, h66, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                            · linarith only [h2, h73, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                              · linarith only [h0, h69, h75, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1, h72, h75, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h7, h72, h9, hc45, hlam, hphi, ht34, u3ehi1]
                        · linarith only [h0, h6, h69, h71, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h69, h70, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                      · linarith only [h69, h81, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h5, h81, h9, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h85 | h85
                · linarith only [h7, h85, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                          · linarith only [h1, h7, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                              · linarith only [h1, h7, h88, h94, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                                · linarith only [h1, h85, h88, h96, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                                  · linarith only [h0, h89, h98, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h2, h93, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h7, h87, h89, h93, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h6, h88, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h88, h89, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h4, h7, h88, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                          · linarith only [h1, h108, h7, h87, hc45, hlam, hphi, ht34, u3ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                            · linarith only [h110, h2, h7, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                              · linarith only [h1, h105, h112, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h114 | h114
                                · linarith only [h1, h105, h114, h85, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                                  · linarith only [h1, h105, h106, h116, h7, h87, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h118 | h118
                                    · linarith only [h1, h105, h118, h7, h87, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h1, h105, h118, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h105, h107, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h105, h106, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h105, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
          · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h126 | h126
          · linarith only [h126, h4, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h128 | h128
            · linarith only [h128, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
              · rcases m.htr 0 3 5 (by decide) (by decide) with h131 | h131
                · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
                    · linarith only [h0, h133, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h135 | h135
                      · linarith only [h0, h126, h135, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                        · linarith only [h0, h128, h137, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h139 | h139
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h143 | h143
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                                    · linarith only [h1, h139, h144, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h140, h144, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h126, h140, h143, h2, hlam]
                                · linarith only [h0, h142, h4, hc35, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h0, h1, h139, h141, h4, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h130, h132, h135, h140, h4, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h130, h133, h139, h4, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
                    · linarith only [h0, h131, h152, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
                      · linarith only [h0, h126, h132, h154, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                        · linarith only [h0, h126, h132, h156, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                            · linarith only [h126, h132, h159, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h163 | h163
                                  · linarith only [h0, h126, h132, h163, hc24, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h126, h163, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h0, h162, h4, hc35, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h0, h1, h158, h161, h4, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h130, h132, h158, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h130, h131, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
                · linarith only [h130, h170, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
                    · linarith only [h0, h126, h173, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h175 | h175
                      · linarith only [h0, h130, h175, h4, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h177 | h177
                        · linarith only [h0, h130, h177, h4, hc34, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                          · linarith only [h1, h130, h179, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h181 | h181
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                              · linarith only [h0, h130, h182, h4, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h182, h4, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h130, h172, h175, h181, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
                    · linarith only [h0, h186, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                      · linarith only [h0, h188, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                        · linarith only [h0, h128, h190, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                          · linarith only [h1, h130, h172, h192, hc45, hlam, hphi, ht34, u3ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                            · linarith only [h130, h172, h194, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                              · linarith only [h0, h130, h196, h4, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h196, h4, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h199 | h199
        · rcases m.htr 0 2 4 (by decide) (by decide) with h200 | h200
          · rcases m.htr 0 2 5 (by decide) (by decide) with h201 | h201
            · linarith only [h0, h201, h3, hlam]
            · linarith only [h200, h201, hc25, hlam, hphi, u2ehi3]
          · linarith only [h199, h200, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h205 | h205
          · linarith only [h199, h205, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h207 | h207
            · linarith only [h199, h207, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h209 | h209
              · rcases m.htr 0 3 5 (by decide) (by decide) with h210 | h210
                · linarith only [h1, h210, h3, hlam]
                · linarith only [h209, h210, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h213 | h213
                · linarith only [h209, h213, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
                  · linarith only [h2, h215, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                    · linarith only [h0, h205, h217, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                      · linarith only [h0, h205, h219, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                        · linarith only [h1, h207, h217, h221, h3, hlam]
                        · linarith only [h1, h217, h221, h3, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h224 | h224
      · rcases m.htr 0 2 3 (by decide) (by decide) with h225 | h225
        · rcases m.htr 0 2 4 (by decide) (by decide) with h226 | h226
          · linarith only [h0, h2, h226, hlam]
          · linarith only [h225, h226, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h229 | h229
          · linarith only [h225, h229, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h231 | h231
            · linarith only [h225, h231, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h233 | h233
              · linarith only [h1, h2, h233, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h235 | h235
                · linarith only [h233, h235, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
                    · linarith only [h0, h2, h225, h238, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                      · linarith only [h0, h1, h2, h225, h229, h240, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1, h2, h238, h240, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h1, h2, h237, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h244 | h244
        · rcases m.htr 0 2 4 (by decide) (by decide) with h245 | h245
          · linarith only [h0, h2, h245, hlam]
          · linarith only [h244, h245, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
          · linarith only [h244, h248, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h250 | h250
            · linarith only [h244, h250, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
              · linarith only [h1, h2, h252, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h254 | h254
                · linarith only [h252, h254, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h257 | h257
                    · linarith only [h0, h2, h257, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h259 | h259
                      · linarith only [h0, h2, h248, h259, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h0, h2, h259, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h256, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h263 | h263
    · rcases m.htr 0 1 5 (by decide) (by decide) with h264 | h264
      · rcases m.htr 0 2 3 (by decide) (by decide) with h265 | h265
        · linarith only [h0, h1, h265, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h267 | h267
          · linarith only [h265, h267, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h269 | h269
            · linarith only [h265, h269, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h271 | h271
              · rcases m.htr 0 3 5 (by decide) (by decide) with h272 | h272
                · rcases m.htr 0 4 5 (by decide) (by decide) with h273 | h273
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
                    · linarith only [h0, h265, h274, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h274, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
                    · linarith only [h0, h1, h265, h277, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h0, h1, h277, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h272, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h271, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h282 | h282
        · linarith only [h0, h1, h282, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h284 | h284
          · linarith only [h282, h284, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
            · linarith only [h282, h286, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h288 | h288
              · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
                · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                  · linarith only [h263, h264, h290, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
                    · linarith only [h0, h1, h292, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1, h292, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h289, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h288, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h297 | h297
      · rcases m.htr 0 2 3 (by decide) (by decide) with h298 | h298
        · linarith only [h0, h1, h298, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h300 | h300
          · linarith only [h298, h300, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h302 | h302
            · linarith only [h298, h302, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h304 | h304
              · rcases m.htr 0 3 5 (by decide) (by decide) with h305 | h305
                · rcases m.htr 0 4 5 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
                    · linarith only [h0, h1, h298, h307, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h307, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h263, h306, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h263, h304, h305, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h304, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
        · linarith only [h0, h1, h313, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h315 | h315
          · linarith only [h313, h315, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h317 | h317
            · linarith only [h313, h317, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h319 | h319
              · rcases m.htr 0 3 5 (by decide) (by decide) with h320 | h320
                · rcases m.htr 0 4 5 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h322 | h322
                    · linarith only [h0, h1, h313, h322, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h322, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h263, h321, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h263, h319, h320, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h319, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h328 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h329 | h329
  · rcases m.htr 0 1 5 (by decide) (by decide) with h330 | h330
    · rcases m.htr 0 2 3 (by decide) (by decide) with h331 | h331
      · rcases m.htr 0 2 4 (by decide) (by decide) with h332 | h332
        · rcases m.htr 0 2 5 (by decide) (by decide) with h333 | h333
          · rcases m.htr 0 3 4 (by decide) (by decide) with h334 | h334
            · rcases m.htr 0 3 5 (by decide) (by decide) with h335 | h335
              · rcases m.htr 0 4 5 (by decide) (by decide) with h336 | h336
                · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h338 | h338
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h339 | h339
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
                        · linarith only [h0, h328, h340, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h328, h334, h337, h340, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h330, h339, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h330, h338, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h328, h337, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h348 | h348
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h349 | h349
                        · linarith only [h0, h328, h349, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h328, h334, h346, h349, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h330, h348, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h328, h346, h347, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h328, h346, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h334, h335, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
              · linarith only [h334, h356, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h358 | h358
                · rcases m.htr 1 2 3 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h360 | h360
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h361 | h361
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h362 | h362
                        · linarith only [h0, h328, h362, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                          · linarith only [h0, h329, h364, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h0, h329, h358, h359, h362, h364, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h330, h361, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h330, h360, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h328, h359, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                        · linarith only [h328, h334, h373, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                          · linarith only [h0, h329, h358, h375, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
                            · linarith only [h328, h334, h370, h377, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h379 | h379
                              · linarith only [h0, h330, h370, h373, h375, h379, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h381 | h381
                                · linarith only [h329, h358, h371, h381, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
                                  · linarith only [h329, h358, h370, h373, h383, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h328, h334, h370, h383, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h330, h372, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h328, h370, h371, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h328, h370, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h331, h333, hc25, hlam, hphi, u2ehi2]
        · linarith only [h331, h332, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h328, h331, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h392 | h392
      · rcases m.htr 0 2 4 (by decide) (by decide) with h393 | h393
        · rcases m.htr 0 2 5 (by decide) (by decide) with h394 | h394
          · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
            · rcases m.htr 0 3 5 (by decide) (by decide) with h396 | h396
              · linarith only [h328, h330, h396, hlam]
              · linarith only [h395, h396, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h399 | h399
              · linarith only [h395, h399, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h401 | h401
                · linarith only [h329, h330, h401, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                        · linarith only [h328, h395, h406, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                          · linarith only [h329, h330, h401, h405, h408, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h329, h330, h403, h406, h408, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h394, h405, hlam]
                    · linarith only [h0, h394, h404, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h394, h403, hc23, hlam, hphi, u2ehi4]
          · linarith only [h392, h394, hc25, hlam, hphi, u2ehi2]
        · linarith only [h392, h393, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h328, h392, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h417 | h417
    · rcases m.htr 0 2 3 (by decide) (by decide) with h418 | h418
      · rcases m.htr 0 2 4 (by decide) (by decide) with h419 | h419
        · rcases m.htr 0 2 5 (by decide) (by decide) with h420 | h420
          · rcases m.htr 0 3 4 (by decide) (by decide) with h421 | h421
            · linarith only [h328, h329, h421, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h423 | h423
              · linarith only [h421, h423, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h425 | h425
                · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h427 | h427
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h428 | h428
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h429 | h429
                        · linarith only [h328, h329, h421, h427, h429, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h329, h417, h428, h429, hc34, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h0, h419, h428, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h0, h417, h427, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h328, h426, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h328, h329, h425, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h418, h420, hc25, hlam, hphi, u2ehi2]
        · linarith only [h418, h419, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h328, h418, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h439 | h439
      · rcases m.htr 0 2 4 (by decide) (by decide) with h440 | h440
        · rcases m.htr 0 2 5 (by decide) (by decide) with h441 | h441
          · rcases m.htr 0 3 4 (by decide) (by decide) with h442 | h442
            · linarith only [h328, h329, h442, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h444 | h444
              · linarith only [h442, h444, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h446 | h446
                · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h450 | h450
                        · linarith only [h328, h442, h450, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h328, h329, h447, h450, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h328, h329, h441, h447, h448, h449, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h328, h440, h447, h448, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h328, h447, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h328, h329, h446, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h439, h441, hc25, hlam, hphi, u2ehi2]
        · linarith only [h439, h440, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h328, h439, hlam]

set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h460 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h461 | h461
  · rcases m.htr 0 2 3 (by decide) (by decide) with h462 | h462
    · rcases m.htr 0 2 4 (by decide) (by decide) with h463 | h463
      · rcases m.htr 0 2 5 (by decide) (by decide) with h464 | h464
        · rcases m.htr 0 3 4 (by decide) (by decide) with h465 | h465
          · rcases m.htr 0 3 5 (by decide) (by decide) with h466 | h466
            · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
              · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h472 | h472
                        · linarith only [h328, h460, h468, h472, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · linarith only [h328, h460, h467, h468, h469, h472, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h328, h461, h471, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h328, h461, h468, h470, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h328, h461, h468, h469, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h462, h468, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
                · rcases m.htr 1 2 4 (by decide) (by decide) with h480 | h480
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h481 | h481
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h482 | h482
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h483 | h483
                        · linarith only [h460, h467, h483, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h485 | h485
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h486 | h486
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                              · linarith only [h460, h467, h480, h487, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h489 | h489
                                · linarith only [h460, h467, h480, h485, h489, hlam]
                                · rcases h0bigk with h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h0, hlam, p491_1]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h328, hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h328, h460, h479, h480, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p491_1, u2ehi3]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h328, h460, h467, h479, h480, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p491_1, u2ehi3]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h0, h461, hc12, hlam, hphi, ht01, ht0b, ht5b, p491_1, u5ehi1]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h0, h328, h461, h481, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p491_1, u2ehi4]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    rcases p491_3 (m.d 0 1) (by simp) with h500 | h500
                                    · linarith only [h0, h500, hlam]
                                    · linarith only [h460, h500, hlam]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    rcases p491_3 (m.d 0 1) (by simp) with h503 | h503
                                    · linarith only [h0, h503, hlam]
                                    · linarith only [h461, h503, hlam]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h461, h480, h483, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p491_1, u2ehi3]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h462, hlam, p491_1]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    rcases p491_3 (m.d 0 1) (by simp) with h509 | h509
                                    · linarith only [h328, h509, hlam]
                                    · linarith only [h460, h509, hlam]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    rcases p491_3 (m.d 0 1) (by simp) with h512 | h512
                                    · linarith only [h328, h512, hlam]
                                    · linarith only [h461, h512, hlam]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h460, hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h463, hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h465, hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h467, hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h461, hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h464, hlam, p491_1]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h466, hlam, p491_0]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [h0, h460, h461, h480, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p491_1, u2ehi3]
                                  · have p491_0 := h491c.1
                                    have p491_1 := h491c.2.1
                                    have p491_2 := h491c.2.2.1
                                    have p491_3 := h491c.2.2.2
                                    linarith only [hlam, p491_0]
                            · linarith only [h328, h461, h466, h479, h485, h486, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h465, h467, h485, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h328, h465, h467, h482, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h328, h460, h479, h480, h481, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h328, h461, h479, h480, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h461, h479, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h465, h466, hc35, hlam, hphi, u3ehi3]
          · linarith only [h328, h460, h465, hlam]
        · linarith only [h462, h464, hc25, hlam, hphi, u2ehi2]
      · linarith only [h462, h463, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h535 | h535
      · linarith only [h462, h535, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h460, h535, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h538 | h538
    · rcases m.htr 0 2 4 (by decide) (by decide) with h539 | h539
      · rcases m.htr 0 2 5 (by decide) (by decide) with h540 | h540
        · rcases m.htr 0 3 4 (by decide) (by decide) with h541 | h541
          · rcases m.htr 0 3 5 (by decide) (by decide) with h542 | h542
            · rcases m.htr 0 4 5 (by decide) (by decide) with h543 | h543
              · linarith only [h460, h461, h543, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h545 | h545
                · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h547 | h547
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h549 | h549
                        · linarith only [h460, h461, h543, h549, hlam]
                        · linarith only [h460, h461, h546, h549, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                      · linarith only [h328, h460, h546, h548, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h0, h460, h540, h546, h547, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h0, h538, h546, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h460, h538, h539, h545, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
            · linarith only [h541, h542, hc35, hlam, hphi, u3ehi3]
          · linarith only [h328, h460, h541, hlam]
        · linarith only [h538, h540, hc25, hlam, hphi, u2ehi2]
      · linarith only [h538, h539, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h560 | h560
      · linarith only [h538, h560, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h460, h560, hlam]

set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h460 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h563 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h564 | h564
  · rcases m.htr 0 2 4 (by decide) (by decide) with h565 | h565
    · rcases m.htr 0 2 5 (by decide) (by decide) with h566 | h566
      · rcases m.htr 0 3 4 (by decide) (by decide) with h567 | h567
        · rcases m.htr 0 3 5 (by decide) (by decide) with h568 | h568
          · rcases m.htr 0 4 5 (by decide) (by decide) with h569 | h569
            · rcases m.htr 1 2 3 (by decide) (by decide) with h570 | h570
              · rcases m.htr 1 2 4 (by decide) (by decide) with h571 | h571
                · rcases m.htr 1 2 5 (by decide) (by decide) with h572 | h572
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h573 | h573
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h575 | h575
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h577 | h577
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h578 | h578
                              · linarith only [h0, h564, h575, h578, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h460, h563, h570, h573, h574, h578, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h460, h563, h570, h573, h574, h577, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h460, h563, h568, h570, h573, h575, h576, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h583 | h583
                          · linarith only [h575, h583, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h585 | h585
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h586 | h586
                              · rcases h0bigk with h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h0, hlam, p587_1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h328, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h460, hlam, p587_1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h460, h568, h570, h573, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p587_1, u2ehi2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h0, h563, hc12, hlam, hphi, ht01, ht0b, ht5b, p587_1, u5ehi1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h0, h567, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p587_1, u3ehi3]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h0, h460, h563, h568, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p587_1, u2ehi2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h0, h568, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p587_1, u2ehi2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h563, h568, h583, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p587_1, u2ehi2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h564, hlam, p587_1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h328, h460, h563, h568, h570, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p587_1, u2ehi2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h328, h568, h570, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p587_1, u2ehi2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h563, h568, h583, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p587_1, u2ehi2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h565, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h567, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h460, h568, h570, h573, h583, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p587_1, u2ehi2]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h563, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h566, hlam, p587_1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h568, hlam, p587_0]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [h569, hlam, p587_1]
                                · have p587_0 := h587c.1
                                  have p587_1 := h587c.2.1
                                  have p587_2 := h587c.2.2.1
                                  have p587_3 := h587c.2.2.2
                                  linarith only [hlam, p587_0]
                              · linarith only [h575, h585, h586, hc24, hlam, hphi, u2ehi2]
                            · linarith only [h460, h563, h570, h573, h574, h585, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h460, h563, h574, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                    · linarith only [h328, h567, h573, hlam]
                  · linarith only [h0, h563, h572, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h328, h563, h570, h571, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h563, h564, h570, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
            · linarith only [h460, h563, h569, hlam]
          · linarith only [h567, h568, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h622 | h622
          · linarith only [h567, h622, hc34, hlam, hphi, u3ehi4]
          · linarith only [h328, h563, h622, hlam]
      · linarith only [h564, h566, hc25, hlam, hphi, u2ehi2]
    · linarith only [h564, h565, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h627 | h627
    · linarith only [h564, h627, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h629 | h629
      · linarith only [h564, h629, hc23, hlam, hphi, u2ehi4]
      · linarith only [h0, h563, h629, hlam]

end R2N4
