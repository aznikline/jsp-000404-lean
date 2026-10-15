import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_I_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h10, h14, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                · linarith only [h0, h14, h16, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                                  · linarith only [h0, h11, h18, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h0, h11, h13, h18, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                              · linarith only [h0, h10, h21, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h11, h13, h21, h23, h4, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                                  · linarith only [h11, h13, h25, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                                    · linarith only [h0, h13, h27, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                                    · linarith only [h21, h27, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h10, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                        · linarith only [h0, h10, h32, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                                · linarith only [h0, h32, h34, h36, h37, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h32, h36, h37, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h0, h10, h34, h36, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                            · linarith only [h32, h34, h35, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                                    · linarith only [h0, h4, h43, h46, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h2, h42, h46, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h32, h4, h45, h7, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                · linarith only [h0, h10, h4, h44, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h10, h43, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                                  · linarith only [h42, h52, h54, hc23, hlam, hphi, ht12, u1ehi3]
                                  · linarith only [h32, h54, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                · linarith only [h32, h52, h53, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h0, h10, h4, h52, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                            · linarith only [h2, h62, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                              · linarith only [h0, h59, h64, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h64, h7, h9, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h0, h59, h6, h61, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h5, h59, h60, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                        · linarith only [h0, h4, h59, h69, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h5, h69, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h73 | h73
                  · linarith only [h7, h73, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                              · linarith only [h7, h76, h80, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                                · linarith only [h0, h73, h77, h80, h82, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
                                  · linarith only [h0, h77, h84, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h2, h79, h84, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h7, h75, h79, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h6, h73, h76, h78, hc35, hlam, hphi, u3ehi2]
                        · linarith only [h0, h5, h76, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h4, h7, h76, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                            · linarith only [h2, h75, h94, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                              · linarith only [h4, h7, h75, h96, hc45, hlam, hphi, ht34, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                                · linarith only [h1, h73, h91, h98, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h100 | h100
                                  · linarith only [h100, h2, h75, h92, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                                    · linarith only [h102, h7, h75, hc34, hlam, hphi, u3ehi0]
                                    · linarith only [h1, h102, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · linarith only [h0, h6, h91, h93, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h5, h91, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h4, h7, h91, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
                · rcases m.htr 0 3 5 (by decide) (by decide) with h109 | h109
                  · linarith only [h109, h4, h6, hlam]
                  · linarith only [h108, h109, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
                  · linarith only [h108, h112, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h114 | h114
                    · linarith only [h114, h5, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                          · linarith only [h0, h118, h6, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                            · linarith only [h1, h108, h114, h120, hc14, hlam, hphi, u1ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                              · linarith only [h122, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
                                · linarith only [h0, h1, h112, h117, h122, h124, h6, hc25, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h0, h117, h122, h124, h6, hc35, hlam, hphi, u3ehi2]
                        · linarith only [h116, h117, h5, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h116, h4, h6, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
              · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
                · linarith only [h130, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
                  · linarith only [h130, h132, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                        · linarith only [h0, h129, h132, h136, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                              · linarith only [h0, h1, h130, h135, h140, h5, hc24, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h135, h140, h5, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h135, h136, h139, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h129, h135, h138, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h135, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h134, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h147 | h147
                · linarith only [h147, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
                  · linarith only [h147, h149, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h151 | h151
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h153 | h153
                        · linarith only [h0, h153, h5, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
                          · linarith only [h0, h129, h155, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                              · linarith only [h0, h147, h152, h158, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h0, h152, h158, h5, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h151, h157, h5, hc24, hlam, hphi, ht12, u1ehi3]
                      · linarith only [h152, h4, h5, hc12, hc24, hlam, hphi]
                    · linarith only [h151, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h164 | h164
            · rcases m.htr 0 2 5 (by decide) (by decide) with h165 | h165
              · rcases m.htr 0 3 4 (by decide) (by decide) with h166 | h166
                · rcases m.htr 0 3 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                      · linarith only [h164, h168, h169, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h176 | h176
                                  · linarith only [h1, h169, h171, h176, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h164, h168, h176, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                                · linarith only [h164, h175, h2, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h0, h171, h173, h174, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h164, h168, h173, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                          · linarith only [h165, h171, h172, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h164, h171, h4, hc12, hc23, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h184 | h184
                      · linarith only [h0, h164, h184, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h186 | h186
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h187 | h187
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h188 | h188
                            · linarith only [h168, h188, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h191 | h191
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                                  · linarith only [h0, h168, h186, h192, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                                    · linarith only [h0, h168, h187, h190, h192, h194, h2, h4, hc23, hlam, hphi, ht12, u1ehi3]
                                    · rcases h0bigk with h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h0, h187, h190, h192, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h0, h187, h190, h192, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h0, h187, h190, h192, h2, h4, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p196_1, u1ehi3, u3ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h0, h187, h188, h190, h192, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p196_1, u1ehi3, u3ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h0, hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h4, hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h2, h4, hc23, hlam, hphi, ht12, p196_1, u1ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h188, h3, h4, hc23, hlam, hphi, ht12, p196_1, u1ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h1, hlam, p196_1]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h0, h187, h190, h192, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h2, h4, hc23, hlam, hphi, ht12, p196_1, u1ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h188, h3, h4, hc23, hlam, hphi, ht12, p196_1, u1ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h2, hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h164, hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h166, hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h168, hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h3, hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h165, hlam, p196_1]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h167, hlam, p196_0]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [h0, h187, h190, h192, h2, h4, hc05, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p196_1, u1ehi3, u3ehi3]
                                      · have p196_0 := h196c.1
                                        have p196_1 := h196c.2.1
                                        have p196_2 := h196c.2.2.1
                                        have p196_3 := h196c.2.2.2
                                        linarith only [hlam, p196_0]
                                · linarith only [h0, h191, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h0, h186, h190, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                          · linarith only [h165, h186, h187, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h164, h186, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h166, h167, hc35, hlam, hphi, u3ehi3]
                · linarith only [h164, h166, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
                · rcases m.htr 0 3 5 (by decide) (by decide) with h229 | h229
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h230 | h230
                    · linarith only [h164, h165, h230, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
                      · linarith only [h0, h232, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h235 | h235
                          · linarith only [h0, h165, h235, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                            · linarith only [h2, h230, h237, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h240 | h240
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h241 | h241
                                  · linarith only [h0, h165, h2, h230, h234, h240, h241, hc23, hlam, hphi, ht12, u1ehi3]
                                  · linarith only [h0, h165, h234, h239, h241, hc45, hlam, hphi, ht34, u3ehi3]
                                · linarith only [h0, h1, h229, h234, h239, h240, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h229, h239, h4, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h164, h165, h234, hc25, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h228, h229, hc35, hlam, hphi, u3ehi3]
                · linarith only [h164, h228, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h249 | h249
              · rcases m.htr 0 3 4 (by decide) (by decide) with h250 | h250
                · rcases m.htr 0 3 5 (by decide) (by decide) with h251 | h251
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h252 | h252
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h253 | h253
                      · linarith only [h249, h253, h3, h4, hc12, hlam, hphi, u1ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h255 | h255
                        · linarith only [h0, h164, h255, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h257 | h257
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h259 | h259
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h261 | h261
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h262 | h262
                                    · rcases h0bigk with h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h0, h257, h260, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p263_1, u3ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h250, h262, hc01, hlam, hphi, ht0b, ht45, ht5b, p263_1, u4ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h0, h164, h257, h260, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p263_1, u3ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h0, h164, h257, h259, h260, h3, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p263_1, u1ehi4, u3ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h0, hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h4, hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h164, hlam, p263_1]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h164, h259, h3, hc23, hlam, hphi, ht12, p263_1, u1ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h1, hlam, p263_1]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h0, h257, h260, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p263_1, u3ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h0, h164, h257, h260, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p263_1, u3ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h3, h4, hc23, hlam, hphi, ht12, p263_1, u1ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h2, hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h0, h257, h260, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p263_1, u3ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h250, hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p263_1, u1ehi4]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h3, hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h249, hlam, p263_1]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h251, hlam, p263_0]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [h252, hlam, p263_1]
                                      · have p263_0 := h263c.1
                                        have p263_1 := h263c.2.1
                                        have p263_2 := h263c.2.2.1
                                        have p263_3 := h263c.2.2.2
                                        linarith only [hlam, p263_0]
                                    · linarith only [h2, h258, h262, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h0, h164, h2, h257, h258, h260, h261, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h0, h164, h259, h260, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h249, h259, h3, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                            · linarith only [h164, h252, h258, hc24, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h249, h257, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h164, h249, h252, hlam]
                  · linarith only [h250, h251, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h297 | h297
                  · linarith only [h250, h297, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h249, h297, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h300 | h300
                · rcases m.htr 0 3 5 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h302 | h302
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
                      · linarith only [h0, h303, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h305 | h305
                        · linarith only [h0, h164, h305, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h307 | h307
                          · linarith only [h0, h249, h307, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h311 | h311
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h313 | h313
                                    · rcases h0bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p314_1, u1ehi1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h300, h313, hc01, hlam, hphi, ht0b, ht45, ht5b, p314_1, u4ehi4]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p314_1, u4ehi0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h3, h307, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p314_1, u1ehi1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h0, hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h4, hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h164, hlam, p314_1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h249, hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h1, hlam, p314_1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p314_1, u1ehi1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h0, h164, h4, hc23, hlam, hphi, ht12, p314_1, u1ehi1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h3, h307, h4, hc23, hlam, hphi, ht12, p314_1, u1ehi1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h2, hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p314_1, u1ehi1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h300, hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h164, h3, h307, h310, hc23, hlam, hphi, ht12, p314_1, u1ehi1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h3, hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p314_1, u1ehi1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h301, hlam, p314_0]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [h302, hlam, p314_1]
                                      · have p314_0 := h314c.1
                                        have p314_1 := h314c.2.1
                                        have p314_2 := h314c.2.2.1
                                        have p314_3 := h314c.2.2.2
                                        linarith only [hlam, p314_0]
                                    · linarith only [h2, h309, h313, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h164, h2, h309, h312, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                                · linarith only [h301, h311, h4, hlam]
                              · linarith only [h301, h310, h4, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h300, h302, h309, h4, hc23, hlam, hphi, ht12, u1ehi3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h345 | h345
                      · linarith only [h0, h164, h301, h345, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
                        · linarith only [h0, h164, h302, h347, hc45, hlam, hphi, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h349 | h349
                          · linarith only [h0, h249, h349, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h351 | h351
                            · linarith only [h0, h164, h302, h351, hc14, hlam, hphi, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                                  · linarith only [h0, h164, h302, h353, h355, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h0, h164, h355, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                · linarith only [h0, h354, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h301, h353, h4, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h300, h301, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h361 | h361
                  · linarith only [h300, h361, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h363 | h363
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h364 | h364
                      · linarith only [h0, h364, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h366 | h366
                        · linarith only [h0, h164, h366, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h368 | h368
                          · linarith only [h0, h249, h368, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h371 | h371
                              · linarith only [h1, h300, h371, hc23, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h371, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h164, h363, h370, hc24, hlam, hphi, ht12, u1ehi3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h375 | h375
                      · linarith only [h0, h375, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h377 | h377
                        · linarith only [h0, h164, h377, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h379 | h379
                          · linarith only [h0, h249, h379, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h381 | h381
                            · linarith only [h0, h300, h363, h381, h4, hc14, hlam, hphi, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
                              · linarith only [h0, h300, h383, h4, hc23, hlam, hphi, ht12, u1ehi1]
                              · linarith only [h0, h383, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h389 | h389
    · linarith only [h0, h389, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h391 | h391
      · linarith only [h0, h391, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h393 | h393
        · linarith only [h0, h393, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h395 | h395
          · rcases m.htr 0 2 4 (by decide) (by decide) with h396 | h396
            · rcases m.htr 0 2 5 (by decide) (by decide) with h397 | h397
              · rcases m.htr 0 3 4 (by decide) (by decide) with h398 | h398
                · rcases m.htr 0 3 5 (by decide) (by decide) with h399 | h399
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h400 | h400
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h403 | h403
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h404 | h404
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h405 | h405
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h406 | h406
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h407 | h407
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h408 | h408
                                    · linarith only [h395, h405, h408, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h0, h395, h405, h407, h408, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h411 | h411
                                    · linarith only [h405, h407, h411, hlam]
                                    · rcases h0bigk with h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [hlam, p413_0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h0, hlam, p413_1]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h389, hlam, p413_0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h391, hlam, p413_1]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h393, hlam, p413_1]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, p413_1, u1ehi0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [hlam, p413_0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h0, h398, h400, h405, h407, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p413_1, u3ehi3]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h0, h400, h405, h407, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p413_1, u3ehi3]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h0, h393, hc12, hlam, hphi, p413_1, u1ehi0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p413_1, u1ehi0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h395, hlam, p413_1]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [hlam, p413_0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h389, h400, h401, h405, h407, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p413_1, u3ehi3]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h389, h393, h401, hc12, hlam, hphi, p413_1, u1ehi0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p413_1, u1ehi0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h396, hlam, p413_0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h398, hlam, p413_0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [hlam, p413_0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h389, h393, h398, h401, hc12, hlam, hphi, p413_1, u1ehi0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h389, h398, h400, h401, h405, h407, hc05, hc12, hlam, hphi, ht0b, ht34, ht45, ht5b, p413_1, u1ehi0, u3ehi3]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h397, hlam, p413_1]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h399, hlam, p413_0]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [h400, hlam, p413_1]
                                      · have p413_0 := h413c.1
                                        have p413_1 := h413c.2.1
                                        have p413_2 := h413c.2.2.1
                                        have p413_3 := h413c.2.2.2
                                        linarith only [hlam, p413_0]
                                · linarith only [h389, h399, h401, h405, h406, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h440 | h440
                                · linarith only [h405, h440, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h442 | h442
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h443 | h443
                                    · rcases h0bigk with h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [hlam, p444_0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h0, hlam, p444_1]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h389, hlam, p444_0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h391, hlam, p444_1]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h393, hlam, p444_1]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [hlam, p444_0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h0, h398, h440, h443, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p444_1, u3ehi2]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p444_1, u4ehi0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h0, h393, hc12, hlam, hphi, p444_1, u1ehi0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h395, hlam, p444_1]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [hlam, p444_0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h389, h401, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p444_1, u4ehi0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h389, h393, h401, hc12, hlam, hphi, p444_1, u1ehi0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h389, h398, h401, h440, h443, hc04, hc12, hlam, hphi, ht0b, ht34, ht45, ht5b, p444_1, u1ehi0, u3ehi2]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h396, hlam, p444_0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h398, hlam, p444_0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [hlam, p444_0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h389, h398, h399, h401, h440, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p444_1, u3ehi2]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h397, hlam, p444_1]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h399, hlam, p444_0]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [h400, hlam, p444_1]
                                      · have p444_0 := h444c.1
                                        have p444_1 := h444c.2.1
                                        have p444_2 := h444c.2.2.1
                                        have p444_3 := h444c.2.2.2
                                        linarith only [hlam, p444_0]
                                    · linarith only [h0, h396, h442, h443, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h471 | h471
                                    · linarith only [h398, h405, h442, h471, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                    · linarith only [h400, h405, h471, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h389, h398, h400, h401, h404, hc12, hlam, hphi, u1ehi3]
                          · linarith only [h0, h403, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h0, h402, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h401, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h478 | h478
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h480 | h480
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h481 | h481
                            · linarith only [h391, h400, h481, hc14, hlam, hphi, u1ehi0]
                            · linarith only [h391, h481, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                          · linarith only [h0, h397, h480, hlam]
                        · linarith only [h0, h396, h479, hlam]
                      · linarith only [h0, h395, h478, hlam]
                  · linarith only [h398, h399, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h488 | h488
                  · linarith only [h398, h488, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h490 | h490
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h493 | h493
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h494 | h494
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h495 | h495
                              · linarith only [h395, h398, h495, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h497 | h497
                                · linarith only [h395, h488, h497, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h499 | h499
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h500 | h500
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
                                        linarith only [h389, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h391, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h393, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, p501_1, u1ehi0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, h389, hc12, hlam, hphi, p501_1, u1ehi0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, h396, h499, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p501_1, u4ehi4]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, h389, h488, hc12, hlam, hphi, p501_1, u1ehi0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p501_1, u1ehi0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h395, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h398, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h488, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p501_1, u1ehi0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h396, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h398, hc34, hlam, hphi, p501_1, u3ehi0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h393, h398, hc34, hlam, hphi, ht12, ht23, p501_1, u1ehi0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p501_1, u1ehi0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h397, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h389, h488, h500, hc34, hlam, hphi, ht12, ht23, p501_1, u1ehi0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h490, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                    · linarith only [h389, h398, h500, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                                  · linarith only [h398, h490, h495, h499, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h398, h490, h494, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h0, h493, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h0, h492, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h491, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h534 | h534
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h535 | h535
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h536 | h536
                            · linarith only [h391, h490, h536, hc14, hlam, hphi, u1ehi0]
                            · linarith only [h391, h536, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                          · linarith only [h389, h397, h533, h535, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                        · linarith only [h0, h534, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h533, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h542 | h542
                · rcases m.htr 0 3 5 (by decide) (by decide) with h543 | h543
                  · linarith only [h395, h397, h543, hlam]
                  · linarith only [h542, h543, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h546 | h546
                  · linarith only [h542, h546, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h548 | h548
                    · linarith only [h396, h397, h548, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h551 | h551
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h552 | h552
                          · linarith only [h396, h397, h552, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h0, h552, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h389, h550, h551, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h395, h550, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h557 | h557
              · rcases m.htr 0 3 4 (by decide) (by decide) with h558 | h558
                · linarith only [h395, h396, h558, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
                  · linarith only [h558, h560, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h562 | h562
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h563 | h563
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h564 | h564
                        · linarith only [h395, h396, h564, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h564, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h395, h563, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h395, h396, h562, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h569 | h569
                · linarith only [h395, h396, h569, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
                  · linarith only [h569, h571, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h575 | h575
                        · linarith only [h0, h396, h575, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h0, h575, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h395, h574, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h395, h396, h573, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h580 | h580
            · rcases m.htr 0 2 5 (by decide) (by decide) with h581 | h581
              · rcases m.htr 0 3 4 (by decide) (by decide) with h582 | h582
                · rcases m.htr 0 3 5 (by decide) (by decide) with h583 | h583
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h584 | h584
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h585 | h585
                      · linarith only [h395, h580, h584, h585, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h585, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                      · linarith only [h0, h395, h588, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h588, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h582, h583, hc35, hlam, hphi, u3ehi3]
                · linarith only [h395, h580, h582, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h593 | h593
                · rcases m.htr 0 3 5 (by decide) (by decide) with h594 | h594
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h595 | h595
                    · linarith only [h580, h581, h595, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h597 | h597
                      · linarith only [h0, h395, h597, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h597, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h593, h594, hc35, hlam, hphi, u3ehi3]
                · linarith only [h395, h580, h593, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h602 | h602
              · rcases m.htr 0 3 4 (by decide) (by decide) with h603 | h603
                · rcases m.htr 0 3 5 (by decide) (by decide) with h604 | h604
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h605 | h605
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                      · linarith only [h0, h395, h606, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h606, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h580, h602, h605, hlam]
                  · linarith only [h603, h604, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h611 | h611
                  · linarith only [h603, h611, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h395, h602, h611, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h614 | h614
                · rcases m.htr 0 3 5 (by decide) (by decide) with h615 | h615
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h616 | h616
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h617 | h617
                      · linarith only [h0, h395, h617, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h617, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
                      · linarith only [h0, h395, h620, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h620, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h614, h615, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h624 | h624
                  · linarith only [h614, h624, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h626 | h626
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h627 | h627
                      · linarith only [h0, h395, h627, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h627, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
                      · linarith only [h0, h395, h630, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h630, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
