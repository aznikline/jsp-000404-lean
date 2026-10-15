import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_14_M_LR_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0ehi := hb0.2.2.1
  have h1bigk := hb1.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h10, h13, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h12, h6, hc14, hlam, hphi, u4elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                          · linarith only [h10, h11, h17, hlam]
                          · linarith only [h17, h6, hc14, hlam, hphi, u4elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h0, h10, h20, h3, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                            · linarith only [h0, h10, h23, h3, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                              · linarith only [h20, h25, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                                · linarith only [h0, h27, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h27, h6, hc24, hlam, hphi, u4elo0]
                          · linarith only [h22, h6, hc14, hlam, hphi, u4elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                        · linarith only [h32, h7, h9, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h34, h8, h9, hlam]
                          · linarith only [h34, h6, hc14, hlam, hphi, u4elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                        · linarith only [h0, h3, h31, h37, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                          · linarith only [h39, h8, h9, hlam]
                          · linarith only [h39, h6, hc14, hlam, hphi, u4elo0]
                  · linarith only [h0, h4, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                  · linarith only [h0, h3, h43, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                    · linarith only [h0, h3, h45, h7, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                                  · linarith only [h1, h47, h53, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h53, h6, hc34, hlam, hphi, u4elo0]
                                · linarith only [h0, h3, h47, h49, h52, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h48, h51, h7, hlam]
                            · linarith only [h0, h3, h47, h49, h5, h50, h7, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h49, h6, hc14, hlam, hphi, u4elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                          · linarith only [h47, h48, h60, hlam]
                          · linarith only [h6, h60, hc14, hlam, hphi, u4elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                        · linarith only [h0, h3, h47, h5, h63, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                            · linarith only [h0, h3, h47, h66, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h66, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h6, h65, hc14, hlam, hphi, u4elo0]
              · linarith only [h6, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo3]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h73 | h73
          · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                · linarith only [h3, h73, h75, h76, hc12, hlam, hphi, ht01, u0ehi9]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h0, h78, h85, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h75, h85, hc24, hlam, hphi, u4elo0]
                              · linarith only [h3, h84, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                            · linarith only [h3, h73, h75, h83, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                          · linarith only [h75, h82, hc14, hlam, hphi, u4elo0]
                        · linarith only [h76, h79, h81, hlam]
                      · linarith only [h76, h78, h80, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                          · linarith only [h78, h79, h95, hlam]
                          · linarith only [h75, h95, hc14, hlam, hphi, u4elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                          · linarith only [h76, h78, h94, h98, hlam]
                          · linarith only [h75, h98, hc14, hlam, hphi, u4elo0]
                      · linarith only [h1, h74, h76, h78, h93, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h3, h73, h78, hc12, hc23, hlam, hphi]
              · linarith only [h75, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h74, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo3]
          · linarith only [h73, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h106 | h106
        · rcases m.htr 0 2 4 (by decide) (by decide) with h107 | h107
          · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
            · rcases m.htr 0 4 5 (by decide) (by decide) with h109 | h109
              · linarith only [h0, h106, h108, h109, h2, hlam]
              · linarith only [h109, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h108, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo3]
          · linarith only [h106, h107, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h114 | h114
          · rcases m.htr 0 3 4 (by decide) (by decide) with h115 | h115
            · rcases m.htr 0 4 5 (by decide) (by decide) with h116 | h116
              · linarith only [h1, h106, h114, h116, h2, hlam]
              · linarith only [h116, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h106, h114, h115, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo3]
          · linarith only [h114, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h121 | h121
      · rcases m.htr 0 2 3 (by decide) (by decide) with h122 | h122
        · linarith only [h0, h1, h122, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h124 | h124
          · rcases m.htr 0 3 4 (by decide) (by decide) with h125 | h125
            · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
              · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                · linarith only [h122, h127, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h132 | h132
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h133 | h133
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h136 | h136
                                · linarith only [h0, h129, h136, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h126, h134, h136, hc34, hlam, hphi, u4elo0]
                              · linarith only [h0, h1, h127, h129, h134, h135, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h127, h134, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h126, h133, hc14, hlam, hphi, u4elo0]
                        · linarith only [h0, h1, h132, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h131, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h145 | h145
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h146 | h146
                          · linarith only [h129, h130, h146, hlam]
                          · linarith only [h126, h144, h146, hc34, hlam, hphi, u4elo0]
                        · linarith only [h1, h145, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h1, h121, h129, h130, h144, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h122, h124, h129, hc12, hc23, hlam, hphi]
              · linarith only [h126, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h125, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo3]
          · linarith only [h124, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h155 | h155
        · linarith only [h0, h1, h155, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h157 | h157
          · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
            · rcases m.htr 0 4 5 (by decide) (by decide) with h159 | h159
              · linarith only [h0, h121, h157, h159, hlam]
              · linarith only [h159, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h0, h1, h157, h158, hc24, hlam, hphi, u4elo3]
          · linarith only [h157, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h164 | h164
    · rcases m.htr 0 1 5 (by decide) (by decide) with h165 | h165
      · rcases m.htr 0 2 3 (by decide) (by decide) with h166 | h166
        · rcases m.htr 0 2 4 (by decide) (by decide) with h167 | h167
          · rcases m.htr 0 3 4 (by decide) (by decide) with h168 | h168
            · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
              · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h179 | h179
                                  · linarith only [h164, h170, h176, h179, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h169, h179, hc34, hlam, hphi, u4elo0]
                                · linarith only [h0, h164, h173, h175, h178, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h0, h164, h174, h177, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h0, h164, h173, h176, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h169, h175, hc14, hlam, hphi, u4elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h186 | h186
                          · linarith only [h173, h174, h186, hlam]
                          · linarith only [h169, h186, hc14, hlam, hphi, u4elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h189 | h189
                        · linarith only [h0, h164, h168, h173, h189, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h191 | h191
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h192 | h192
                            · linarith only [h166, h173, h192, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                              · linarith only [h170, h189, h194, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h197 | h197
                                  · rcases h1bigk with h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h0, hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      rcases p198_3 (m.d 0 1) (by simp) with h201 | h201
                                      · rcases p198_3 (m.d 1 2) (by simp) with h202 | h202
                                        · rcases p198_3 (m.d 1 3) (by simp) with h203 | h203
                                          · linarith only [h203, hlam, p198_0]
                                          · rcases p198_3 (m.d 1 4) (by simp) with h205 | h205
                                            · linarith only [h170, h205, hc23, hlam, hphi, ht34, p198_1, u4elo1]
                                            · linarith only [h173, h205, hlam]
                                        · linarith only [h170, h202, hlam]
                                      · linarith only [h201, hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h171, h196, hc45, hlam, hphi, ht0b, ht5b, p198_1, u0elo0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      rcases p198_3 (m.d 0 1) (by simp) with h211 | h211
                                      · rcases p198_3 (m.d 1 2) (by simp) with h212 | h212
                                        · rcases p198_3 (m.d 1 3) (by simp) with h213 | h213
                                          · linarith only [h164, h213, hlam]
                                          · rcases p198_3 (m.d 1 4) (by simp) with h215 | h215
                                            · linarith only [h164, h168, h170, h189, h197, h215, hc23, hlam, hphi, ht34, u4elo1]
                                            · linarith only [h191, h215, hlam]
                                        · linarith only [h172, h212, hlam]
                                      · linarith only [h211, hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p198_1, u0ehi5]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h0, h164, h168, h189, h197, hlam, p198_2]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      rcases p198_3 (m.d 0 1) (by simp) with h223 | h223
                                      · linarith only [h0, h223, hlam]
                                      · linarith only [h164, h168, h173, h223, hlam]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      rcases p198_3 (m.d 0 1) (by simp) with h226 | h226
                                      · linarith only [h0, h226, hlam]
                                      · linarith only [h165, h226, hlam]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h164, hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h170, hlam, p198_1]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h173, hlam, p198_1]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h189, hlam, p198_1]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h164, h168, h173, hlam, p198_1]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h171, hlam, p198_1]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h164, h168, h170, h173, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p198_1, u0elo0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h0, h164, h168, h173, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p198_1]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h165, hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h172, hlam, p198_1]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h0, h165, h170, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p198_1]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [h191, hlam, p198_0]
                                    · have p198_0 := h198c.1
                                      have p198_1 := h198c.2.1
                                      have p198_2 := h198c.2.2.1
                                      have p198_3 := h198c.2.2.2
                                      linarith only [hlam, p198_0]
                                  · linarith only [h173, h196, h197, hc14, hlam, hphi, u4elo2]
                                · linarith only [h191, h192, h196, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h169, h191, hc14, hlam, hphi, u4elo0]
                    · linarith only [h0, h172, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h164, h168, h169, h171, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h0, h164, h168, h169, h170, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h169, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h168, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo3]
          · linarith only [h166, h167, hc23, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h164, h166, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h254 | h254
        · rcases m.htr 0 2 4 (by decide) (by decide) with h255 | h255
          · rcases m.htr 0 3 4 (by decide) (by decide) with h256 | h256
            · rcases m.htr 0 4 5 (by decide) (by decide) with h257 | h257
              · linarith only [h164, h165, h256, h257, hlam]
              · linarith only [h257, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h256, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo3]
          · linarith only [h254, h255, hc23, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h164, h254, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h263 | h263
      · rcases m.htr 0 2 3 (by decide) (by decide) with h264 | h264
        · rcases m.htr 0 2 4 (by decide) (by decide) with h265 | h265
          · rcases m.htr 0 3 4 (by decide) (by decide) with h266 | h266
            · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
              · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
                · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h270 | h270
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h271 | h271
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h272 | h272
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h273 | h273
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h276 | h276
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                                  · linarith only [h264, h274, h277, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h267, h277, hc34, hlam, hphi, u4elo0]
                                · linarith only [h273, h276, hc24, hlam, hphi, u4elo1]
                              · linarith only [h164, h263, h264, h272, h274, h275, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
                              · linarith only [h264, h266, h274, h282, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h284 | h284
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h285 | h285
                                  · rcases h1bigk with h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h0, hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h164, hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h164, h264, h269, h284, hc45, hlam, hphi, ht0b, ht5b, p286_1, u0elo1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h164, h264, h272, h282, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p286_1, u0elo1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p286_1, u0ehi5]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h164, h263, h272, h282, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p286_1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      rcases p286_3 (m.d 0 1) (by simp) with h295 | h295
                                      · linarith only [h0, h295, hlam]
                                      · linarith only [h263, h272, h282, h295, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p286_1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      rcases p286_3 (m.d 0 1) (by simp) with h298 | h298
                                      · linarith only [h0, h298, hlam]
                                      · linarith only [h263, h298, hlam]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h263, h272, h282, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p286_1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h268, hlam, p286_1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      rcases p286_3 (m.d 0 1) (by simp) with h304 | h304
                                      · linarith only [h164, h304, hlam]
                                      · linarith only [h263, h268, h272, h282, h304, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p286_1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      rcases p286_3 (m.d 0 1) (by simp) with h307 | h307
                                      · linarith only [h164, h307, hlam]
                                      · linarith only [h263, h307, hlam]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h263, h272, h282, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p286_1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h269, hlam, p286_1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h271, hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h272, h282, hc23, hlam, hphi, ht34, p286_1, u4elo1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h263, hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h270, hlam, p286_1]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h272, hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [h273, hlam, p286_0]
                                    · have p286_0 := h286c.1
                                      have p286_1 := h286c.2.1
                                      have p286_2 := h286c.2.2.1
                                      have p286_3 := h286c.2.2.2
                                      linarith only [hlam, p286_0]
                                  · linarith only [h284, h285, hc34, hlam, hphi, u4elo2]
                                · linarith only [h273, h284, hc24, hlam, hphi, u4elo1]
                          · linarith only [h267, h273, hc14, hlam, hphi, u4elo0]
                        · linarith only [h164, h272, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h164, h263, h271, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h0, h263, h270, hc25, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h164, h263, h268, h269, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h0, h263, h268, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h267, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h266, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo3]
          · linarith only [h264, h265, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h331 | h331
          · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
            · rcases m.htr 0 4 5 (by decide) (by decide) with h333 | h333
              · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
                · linarith only [h0, h263, h264, h334, hc12, hlam, hphi, ht01, u0ehi9]
                · linarith only [h0, h263, h334, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h333, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h0, h263, h264, h332, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9, u4elo3]
          · linarith only [h0, h263, h331, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h340 | h340
        · rcases m.htr 0 2 4 (by decide) (by decide) with h341 | h341
          · rcases m.htr 0 3 4 (by decide) (by decide) with h342 | h342
            · rcases m.htr 0 4 5 (by decide) (by decide) with h343 | h343
              · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
                · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h349 | h349
                          · linarith only [h263, h349, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5, u4elo1]
                          · linarith only [h343, h349, hc14, hlam, hphi, u4elo0]
                        · linarith only [h164, h348, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h164, h340, h342, h347, hlam, hphi, u0ehi5, u0elo1]
                    · linarith only [h164, h344, h346, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h164, h344, h345, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h340, h344, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h343, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h342, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo3]
          · linarith only [h340, h341, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h360 | h360
          · rcases m.htr 0 3 4 (by decide) (by decide) with h361 | h361
            · rcases m.htr 0 4 5 (by decide) (by decide) with h362 | h362
              · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                · linarith only [h263, h340, h360, h362, h363, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h363, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h362, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
            · linarith only [h0, h340, h361, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5, u4elo3]
          · linarith only [h0, h360, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5, u4elo2]

theorem r1l7_20_12_14_H_R_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h11, h14, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h11, h13, h14, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h10, h13, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                            · linarith only [h11, h12, h18, hlam]
                            · linarith only [h0, h10, h18, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h11, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                            · linarith only [h0, h10, h22, h24, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                              · linarith only [h0, h10, h22, h26, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases h4bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  rcases p28_3 (m.d 0 4) (by simp) with h30 | h30
                                  · rcases p28_3 (m.d 1 4) (by simp) with h31 | h31
                                    · linarith only [h2, h31, hlam]
                                    · rcases p28_3 (m.d 2 4) (by simp) with h33 | h33
                                      · linarith only [h33, h4, hlam]
                                      · rcases p28_3 (m.d 3 4) (by simp) with h35 | h35
                                        · linarith only [h35, h5, hlam]
                                        · rcases p28_3 (m.d 4 5) (by simp) with h37 | h37
                                          · linarith only [h37, h6, hlam]
                                          · linarith only [h10, h37, hlam]
                                  · linarith only [h2, h30, hlam]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  rcases p28_3 (m.d 0 4) (by simp) with h41 | h41
                                  · rcases p28_3 (m.d 1 4) (by simp) with h42 | h42
                                    · linarith only [h2, h42, hlam]
                                    · linarith only [h42, h8, hlam]
                                  · linarith only [h4, h41, hlam]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  rcases p28_3 (m.d 0 4) (by simp) with h46 | h46
                                  · rcases p28_3 (m.d 1 4) (by simp) with h47 | h47
                                    · linarith only [h2, h47, hlam]
                                    · linarith only [h47, h9, hlam]
                                  · linarith only [h46, h5, hlam]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h0, h10, h3, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi3]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h2, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h10, hc45, hlam, hphi, ht23, ht34, p28_1, u2ehi3]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h0, h10, h3, h5, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h10, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h4, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h8, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h24, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h5, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h9, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h22, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h26, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h6, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h0, h3, h5, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi3]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h0, h3, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi3]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  rcases p28_3 (m.d 0 4) (by simp) with h70 | h70
                                  · rcases p28_3 (m.d 1 4) (by simp) with h71 | h71
                                    · linarith only [h10, h71, hlam]
                                    · linarith only [h71, h9, hlam]
                                  · linarith only [h5, h70, hlam]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                            · linarith only [h10, h76, h8, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                              · linarith only [h10, h78, h8, hc34, hlam, hphi, ht23, u2ehi3]
                              · rcases h4bigk with h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  rcases p80_3 (m.d 0 4) (by simp) with h82 | h82
                                  · rcases p80_3 (m.d 1 4) (by simp) with h83 | h83
                                    · linarith only [h2, h83, hlam]
                                    · rcases p80_3 (m.d 2 4) (by simp) with h85 | h85
                                      · linarith only [h4, h85, hlam]
                                      · rcases p80_3 (m.d 3 4) (by simp) with h87 | h87
                                        · linarith only [h5, h87, hlam]
                                        · rcases p80_3 (m.d 4 5) (by simp) with h89 | h89
                                          · linarith only [h6, h89, hlam]
                                          · linarith only [h10, h89, hlam]
                                  · linarith only [h2, h82, hlam]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  rcases p80_3 (m.d 0 4) (by simp) with h93 | h93
                                  · rcases p80_3 (m.d 1 4) (by simp) with h94 | h94
                                    · linarith only [h2, h94, hlam]
                                    · linarith only [h8, h94, hlam]
                                  · linarith only [h4, h93, hlam]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h22, h23, h6, h78, hlam, p80_2]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h0, h22, h23, h3, h5, h78, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p80_1]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h2, hlam, p80_1]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi3]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h10, hc34, hc45, hlam, hphi, p80_1]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h10, hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h4, hlam, p80_1]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h8, hlam, p80_1]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h0, h22, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p80_1]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h76, hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h5, hlam, p80_1]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h9, hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h22, hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h78, hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h6, hlam, p80_0]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h0, h3, h5, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi3]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [h0, h3, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi3]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  rcases p80_3 (m.d 0 4) (by simp) with h118 | h118
                                  · rcases p80_3 (m.d 1 4) (by simp) with h119 | h119
                                    · linarith only [h10, h119, hlam]
                                    · linarith only [h119, h9, hlam]
                                  · linarith only [h118, h5, hlam]
                                · have p80_0 := h80c.1
                                  have p80_1 := h80c.2.1
                                  have p80_2 := h80c.2.2.1
                                  have p80_3 := h80c.2.2.2
                                  linarith only [hlam, p80_0]
                        · linarith only [h0, h22, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h125 | h125
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                        · linarith only [h0, h126, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                              · rcases h4bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [hlam, p131_0]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  rcases p131_3 (m.d 0 4) (by simp) with h133 | h133
                                  · rcases p131_3 (m.d 1 4) (by simp) with h134 | h134
                                    · linarith only [h134, h2, hlam]
                                    · rcases p131_3 (m.d 2 4) (by simp) with h136 | h136
                                      · linarith only [h136, h4, hlam]
                                      · rcases p131_3 (m.d 3 4) (by simp) with h138 | h138
                                        · linarith only [h138, h5, hlam]
                                        · linarith only [h138, h9, hlam]
                                  · linarith only [h133, h2, hlam]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  rcases p131_3 (m.d 0 4) (by simp) with h142 | h142
                                  · rcases p131_3 (m.d 1 4) (by simp) with h143 | h143
                                    · linarith only [h143, h2, hlam]
                                    · linarith only [h143, h8, hlam]
                                  · linarith only [h142, h4, hlam]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h0, h128, h3, h5, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi4]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  rcases p131_3 (m.d 0 4) (by simp) with h148 | h148
                                  · rcases p131_3 (m.d 1 4) (by simp) with h149 | h149
                                    · linarith only [h149, h2, hlam]
                                    · linarith only [h125, h149, hlam]
                                  · linarith only [h148, hlam, p131_0]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h2, hlam, p131_1]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [hlam, p131_0]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h126, h128, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p131_1]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h9, hlam, p131_1]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  rcases p131_3 (m.d 0 4) (by simp) with h157 | h157
                                  · rcases p131_3 (m.d 1 4) (by simp) with h158 | h158
                                    · rcases p131_3 (m.d 2 4) (by simp) with h159 | h159
                                      · linarith only [h159, h8, hlam]
                                      · linarith only [h129, h159, hlam]
                                    · linarith only [h158, hlam, p131_0]
                                  · linarith only [h157, h6, hlam]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h4, hlam, p131_1]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h8, hlam, p131_1]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [hlam, p131_0]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h126, hlam, p131_1]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h0, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p131_1]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h5, hlam, p131_1]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h0, h3, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi3]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi3]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [hlam, p131_0]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  rcases p131_3 (m.d 0 4) (by simp) with h173 | h173
                                  · rcases p131_3 (m.d 1 4) (by simp) with h174 | h174
                                    · linarith only [h174, h9, hlam]
                                    · linarith only [h125, h174, hlam]
                                  · linarith only [h173, h6, hlam]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h6, hlam, p131_0]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h125, hlam, p131_0]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h129, hlam, p131_0]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [h130, hlam, p131_0]
                                · have p131_0 := h131c.1
                                  have p131_1 := h131c.2.1
                                  have p131_2 := h131c.2.2.1
                                  have p131_3 := h131c.2.2.2
                                  linarith only [hlam, p131_0]
                              · linarith only [h128, h130, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                            · linarith only [h125, h126, h128, h129, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                              · rcases h4bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [hlam, p187_0]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  rcases p187_3 (m.d 0 4) (by simp) with h189 | h189
                                  · rcases p187_3 (m.d 1 4) (by simp) with h190 | h190
                                    · linarith only [h190, h2, hlam]
                                    · rcases p187_3 (m.d 2 4) (by simp) with h192 | h192
                                      · linarith only [h192, h4, hlam]
                                      · rcases p187_3 (m.d 3 4) (by simp) with h194 | h194
                                        · linarith only [h194, h5, hlam]
                                        · linarith only [h194, h9, hlam]
                                  · linarith only [h189, h2, hlam]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  rcases p187_3 (m.d 0 4) (by simp) with h198 | h198
                                  · rcases p187_3 (m.d 1 4) (by simp) with h199 | h199
                                    · linarith only [h199, h2, hlam]
                                    · linarith only [h199, h8, hlam]
                                  · linarith only [h198, h4, hlam]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h0, h3, h5, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p187_1, u2ehi2]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  rcases p187_3 (m.d 0 4) (by simp) with h204 | h204
                                  · rcases p187_3 (m.d 1 4) (by simp) with h205 | h205
                                    · linarith only [h2, h205, hlam]
                                    · linarith only [h125, h205, hlam]
                                  · linarith only [h204, hlam, p187_0]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h2, hlam, p187_1]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [hlam, p187_0]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h185, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p187_1]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h9, hlam, p187_1]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  rcases p187_3 (m.d 0 4) (by simp) with h213 | h213
                                  · rcases p187_3 (m.d 1 4) (by simp) with h214 | h214
                                    · rcases p187_3 (m.d 2 4) (by simp) with h215 | h215
                                      · linarith only [h215, h8, hlam]
                                      · linarith only [h185, h215, hlam]
                                    · linarith only [h214, hlam, p187_0]
                                  · linarith only [h213, h6, hlam]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h4, hlam, p187_1]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h8, hlam, p187_1]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [hlam, p187_0]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h126, hlam, p187_1]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h0, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p187_1]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h5, hlam, p187_1]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h0, h3, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p187_1, u2ehi3]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p187_1, u2ehi3]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [hlam, p187_0]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  rcases p187_3 (m.d 0 4) (by simp) with h229 | h229
                                  · rcases p187_3 (m.d 1 4) (by simp) with h230 | h230
                                    · linarith only [h230, h9, hlam]
                                    · linarith only [h125, h230, hlam]
                                  · linarith only [h229, h6, hlam]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h6, hlam, p187_0]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h125, hlam, p187_0]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h185, hlam, p187_0]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [h186, hlam, p187_0]
                                · have p187_0 := h187c.1
                                  have p187_1 := h187c.2.1
                                  have p187_2 := h187c.2.2.1
                                  have p187_3 := h187c.2.2.2
                                  linarith only [hlam, p187_0]
                              · linarith only [h186, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h125, h185, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h241 | h241
                        · linarith only [h241, h7, h9, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h243 | h243
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h244 | h244
                            · linarith only [h0, h125, h244, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h241, h243, h244, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h247 | h247
                            · linarith only [h125, h247, h7, h9, hc24, hlam, hphi, u2ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h249 | h249
                              · linarith only [h125, h249, h7, h9, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h249, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h4, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
                  · linarith only [h253, h7, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h255 | h255
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h256 | h256
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h257 | h257
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h258 | h258
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h259 | h259
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                              · rcases h4bigk with h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  rcases p261_3 (m.d 0 4) (by simp) with h263 | h263
                                  · rcases p261_3 (m.d 1 4) (by simp) with h264 | h264
                                    · linarith only [h2, h264, hlam]
                                    · rcases p261_3 (m.d 2 4) (by simp) with h266 | h266
                                      · linarith only [h266, h4, hlam]
                                      · linarith only [h253, h266, hlam]
                                  · linarith only [h2, h263, hlam]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h0, h253, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p261_1, u2ehi1]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  rcases p261_3 (m.d 0 4) (by simp) with h271 | h271
                                  · rcases p261_3 (m.d 1 4) (by simp) with h272 | h272
                                    · linarith only [h2, h272, hlam]
                                    · linarith only [h255, h272, hlam]
                                  · linarith only [h271, h5, hlam]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  rcases p261_3 (m.d 0 4) (by simp) with h276 | h276
                                  · rcases p261_3 (m.d 1 4) (by simp) with h277 | h277
                                    · linarith only [h2, h277, hlam]
                                    · linarith only [h256, h277, hlam]
                                  · linarith only [h276, hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h2, hlam, p261_1]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h253, hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h2, h260, hc01, hc45, hlam, hphi, ht0b, ht5b, p261_1]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  rcases p261_3 (m.d 0 4) (by simp) with h285 | h285
                                  · rcases p261_3 (m.d 1 4) (by simp) with h286 | h286
                                    · rcases p261_3 (m.d 2 4) (by simp) with h287 | h287
                                      · rcases p261_3 (m.d 3 4) (by simp) with h288 | h288
                                        · linarith only [h255, h288, hlam]
                                        · linarith only [h260, h288, hlam]
                                      · linarith only [h259, h287, hlam]
                                    · linarith only [h286, hlam, p261_0]
                                  · linarith only [h285, h6, hlam]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h4, hlam, p261_1]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h0, h253, h257, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p261_1, u2ehi1]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h0, h257, h260, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p261_1]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  rcases p261_3 (m.d 0 4) (by simp) with h298 | h298
                                  · rcases p261_3 (m.d 1 4) (by simp) with h299 | h299
                                    · linarith only [h253, h299, hlam]
                                    · linarith only [h256, h299, hlam]
                                  · linarith only [h298, h6, hlam]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h5, hlam, p261_1]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h255, hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h257, hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h0, h255, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p261_1]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h6, hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h256, hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h259, hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [h260, hlam, p261_0]
                                · have p261_0 := h261c.1
                                  have p261_1 := h261c.2.1
                                  have p261_2 := h261c.2.2.1
                                  have p261_3 := h261c.2.2.2
                                  linarith only [hlam, p261_0]
                              · rcases h4bigk with h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h256, h260, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, h253, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p313_1, u2ehi1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  rcases p313_3 (m.d 0 4) (by simp) with h317 | h317
                                  · rcases p313_3 (m.d 1 4) (by simp) with h318 | h318
                                    · linarith only [h2, h318, hlam]
                                    · linarith only [h255, h318, hlam]
                                  · linarith only [h317, h5, hlam]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  rcases p313_3 (m.d 0 4) (by simp) with h322 | h322
                                  · rcases p313_3 (m.d 1 4) (by simp) with h323 | h323
                                    · linarith only [h2, h323, hlam]
                                    · linarith only [h256, h323, hlam]
                                  · linarith only [h322, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h2, hlam, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h253, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  rcases p313_3 (m.d 0 4) (by simp) with h330 | h330
                                  · rcases p313_3 (m.d 1 4) (by simp) with h331 | h331
                                    · rcases p313_3 (m.d 2 4) (by simp) with h332 | h332
                                      · rcases p313_3 (m.d 3 4) (by simp) with h333 | h333
                                        · linarith only [h255, h333, hlam]
                                        · rcases p313_3 (m.d 4 5) (by simp) with h335 | h335
                                          · linarith only [h256, h335, hlam]
                                          · linarith only [h260, h335, hlam]
                                      · linarith only [h257, h332, hlam]
                                    · linarith only [h255, h331, hlam]
                                  · linarith only [h330, h5, hlam]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h2, h260, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h4, hlam, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, h253, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p313_1, u2ehi1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  rcases p313_3 (m.d 0 4) (by simp) with h345 | h345
                                  · rcases p313_3 (m.d 1 4) (by simp) with h346 | h346
                                    · linarith only [h253, h346, hlam]
                                    · linarith only [h255, h346, hlam]
                                  · linarith only [h345, h5, hlam]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, h257, h260, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h5, hlam, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h255, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h257, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h260, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h6, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h256, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h259, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h2, h256, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                            · linarith only [h253, h256, h259, hlam]
                          · linarith only [h258, h7, hc35, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h257, h7, hc34, hlam, hphi, ht23, u2ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
                            · linarith only [h253, h256, h364, h366, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h0, h253, h3, h366, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h365, h7, hc35, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h255, h364, h7, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h371 | h371
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
                        · linarith only [h255, h372, h7, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h3, h372, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
                        · linarith only [h255, h375, h7, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h3, h375, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · linarith only [h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc24, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc14, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

end R2N4
