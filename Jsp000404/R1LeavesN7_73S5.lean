import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_L_L_0_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h3, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h12, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h17, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h22, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h20, h21, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                    · linarith only [h0, h27, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h27, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                    · linarith only [h0, h30, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h3, h30, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 3 5 (by decide) (by decide) with h34 | h34
                · linarith only [h3, h34, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                  · linarith only [h3, h33, h36, h5, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                    · linarith only [h0, h38, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h38, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h41 | h41
                · linarith only [h33, h4, h41, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
                  · linarith only [h4, h43, h5, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                    · linarith only [h0, h45, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h45, h5, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h48 | h48
            · rcases m.htr 0 3 4 (by decide) (by decide) with h49 | h49
              · linarith only [h3, h4, h49, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
                · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                    · linarith only [h0, h53, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h53, hc12, hlam, hphi, u2elo3]
                  · linarith only [h3, h4, h51, h52, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                    · linarith only [h0, h58, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h58, hc12, hlam, hphi, u2elo3]
                  · linarith only [h4, h48, h57, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h62 | h62
              · linarith only [h3, h4, h62, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
                · linarith only [h3, h48, h64, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                    · linarith only [h0, h67, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h67, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                    · linarith only [h0, h70, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h70, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h73 | h73
          · rcases m.htr 0 2 5 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                    · linarith only [h0, h78, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                      · linarith only [h1, h78, h80, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h73, h80, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
                    · linarith only [h3, h83, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                      · linarith only [h1, h83, h85, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h73, h85, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h3, h74, h76, hlam]
              · linarith only [h3, h73, h75, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
              · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
                · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
                  · linarith only [h73, h74, h92, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                    · linarith only [h0, h94, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                      · linarith only [h1, h94, h96, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h3, h73, h96, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h99 | h99
                  · linarith only [h3, h73, h91, h99, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                    · linarith only [h0, h101, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                      · linarith only [h1, h101, h103, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h103, h3, h73, h91, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h3, h73, h90, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h107 | h107
            · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 3 5 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 4 5 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                    · linarith only [h111, h3, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                      · linarith only [h1, h111, h113, h73, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                        · linarith only [h1, h111, h115, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h107, h115, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h107, h110, h73, hlam]
                · linarith only [h107, h108, h109, h73, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h120 | h120
                · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                    · linarith only [h0, h122, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                      · linarith only [h1, h122, h124, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                        · linarith only [h1, h122, h126, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h107, h126, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h107, h108, h121, h3, hlam]
                · linarith only [h107, h120, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
              · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
                · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                    · linarith only [h0, h134, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                      · linarith only [h1, h134, h136, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                        · linarith only [h1, h107, h134, h138, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                          · linarith only [h1, h140, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h131, h140, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
                    · linarith only [h0, h143, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                      · linarith only [h145, h73, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                        · linarith only [h0, h107, h147, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                          · linarith only [h1, h149, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h131, h149, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h152 | h152
                  · linarith only [h131, h132, h152, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                    · linarith only [h0, h154, h3, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                      · linarith only [h0, h156, h73, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h158 | h158
                        · linarith only [h0, h107, h158, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                          · linarith only [h1, h160, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h131, h132, h160, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                    · linarith only [h0, h165, h3, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                      · linarith only [h0, h167, h73, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                        · linarith only [h0, h107, h169, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                          · linarith only [h131, h171, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                            · linarith only [h1, h173, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h163, h173, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h131, h163, h164, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                    · linarith only [h0, h178, h3, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                      · linarith only [h0, h180, h73, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                        · linarith only [h0, h107, h182, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                          · linarith only [h131, h184, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                            · linarith only [h1, h163, h186, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h188 | h188
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h189 | h189
                                · linarith only [h0, h131, h189, h3, hc12, hlam, hphi, u2elo2]
                                · linarith only [h0, h189, h3, hc12, hlam, hphi, ht23, u3elo3]
                              · linarith only [h177, h188, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
                    · linarith only [h0, h193, h3, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
                      · linarith only [h0, h195, h73, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                        · linarith only [h1, h107, h193, h197, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
                          · linarith only [h1, h199, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                            · linarith only [h1, h163, h201, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                              · linarith only [h0, h131, h177, h195, h203, h3, hc12, hlam, hphi, u2elo3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                                · linarith only [h0, h131, h205, h3, hc12, hlam, hphi, u2elo2]
                                · linarith only [h0, h205, h3, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h208 | h208
        · rcases m.htr 0 2 4 (by decide) (by decide) with h209 | h209
          · rcases m.htr 0 2 5 (by decide) (by decide) with h210 | h210
            · linarith only [h0, h2, h210, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 3 5 (by decide) (by decide) with h213 | h213
                · linarith only [h1, h2, h213, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
                  · linarith only [h0, h2, h209, h215, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                    · linarith only [h0, h217, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h208, h210, h217, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h220 | h220
                · linarith only [h1, h2, h212, h220, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h222 | h222
                  · linarith only [h0, h2, h209, h210, h222, hc12, hlam, hphi, u2elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                    · linarith only [h0, h224, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h208, h210, h224, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h227 | h227
            · linarith only [h0, h2, h209, h227, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h229 | h229
              · linarith only [h208, h209, h229, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h231 | h231
                · linarith only [h0, h2, h208, h209, h231, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h233 | h233
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                    · linarith only [h0, h234, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h208, h209, h234, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                    · linarith only [h0, h237, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h208, h209, h237, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h240 | h240
          · rcases m.htr 0 2 5 (by decide) (by decide) with h241 | h241
            · linarith only [h0, h2, h208, h241, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h243 | h243
              · rcases m.htr 0 3 5 (by decide) (by decide) with h244 | h244
                · linarith only [h1, h2, h244, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h246 | h246
                  · linarith only [h0, h2, h208, h240, h244, h246, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
                    · linarith only [h0, h208, h240, h244, h248, hc23, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                      · linarith only [h0, h2, h250, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h208, h240, h244, h250, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h208, h240, h243, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h254 | h254
            · linarith only [h1, h2, h208, h254, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h256 | h256
              · rcases m.htr 0 3 5 (by decide) (by decide) with h257 | h257
                · linarith only [h1, h2, h257, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h259 | h259
                  · linarith only [h0, h2, h256, h257, h259, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
                    · linarith only [h0, h261, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
                      · linarith only [h240, h263, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
                        · linarith only [h1, h2, h254, h261, h265, hlam]
                        · linarith only [h1, h2, h261, h265, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
                · linarith only [h1, h2, h256, h268, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                    · linarith only [h0, h2, h270, h271, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                      · linarith only [h1, h2, h240, h270, h271, h273, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
                        · linarith only [h1, h2, h270, h271, h275, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h1, h2, h271, h275, hc12, hlam, hphi, u2elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h278 | h278
                    · linarith only [h0, h208, h278, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h280 | h280
                      · linarith only [h0, h2, h240, h280, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h1, h2, h278, h282, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h1, h2, h278, h282, hc12, hlam, hphi, u2elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h286 | h286
    · rcases m.htr 0 1 5 (by decide) (by decide) with h287 | h287
      · rcases m.htr 0 2 3 (by decide) (by decide) with h288 | h288
        · rcases m.htr 0 2 4 (by decide) (by decide) with h289 | h289
          · rcases m.htr 0 2 5 (by decide) (by decide) with h290 | h290
            · rcases m.htr 0 3 4 (by decide) (by decide) with h291 | h291
              · rcases m.htr 0 3 5 (by decide) (by decide) with h292 | h292
                · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h295 | h295
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h296 | h296
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h297 | h297
                          · linarith only [h286, h297, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h291, h297, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h296, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h286, h294, h295, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h294, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                          · linarith only [h286, h306, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h291, h306, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h305, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h289, h304, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h286, h303, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
                  · linarith only [h291, h292, h312, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h317 | h317
                          · linarith only [h286, h317, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h291, h317, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h286, h314, h316, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h315, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h314, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h323 | h323
                · rcases m.htr 0 4 5 (by decide) (by decide) with h324 | h324
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h326 | h326
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h327 | h327
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h328 | h328
                          · linarith only [h286, h291, h323, h328, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h330 | h330
                            · linarith only [h0, h286, h330, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h323, h330, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h286, h325, h327, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h286, h289, h325, h326, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h325, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h291, h323, h324, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h337 | h337
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h338 | h338
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h339 | h339
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h340 | h340
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h341 | h341
                          · linarith only [h286, h291, h341, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h343 | h343
                            · linarith only [h286, h323, h343, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h345 | h345
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h346 | h346
                                · linarith only [h286, h291, h338, h346, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h348 | h348
                                  · linarith only [h286, h323, h338, h348, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
                                    · linarith only [h289, h350, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h337, h350, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                              · linarith only [h289, h337, h345, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h0, h340, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h286, h338, h339, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h338, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h357 | h357
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h358 | h358
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h359 | h359
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
                          · linarith only [h286, h360, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
                            · linarith only [h286, h323, h362, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                              · linarith only [h291, h337, h360, h364, hc03, hlam, hphi, u3elo3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                                · linarith only [h0, h286, h357, h366, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h368 | h368
                                  · linarith only [h286, h323, h357, h368, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h370 | h370
                                    · linarith only [h289, h291, h337, h370, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h372 | h372
                                      · linarith only [h286, h291, h337, h357, h372, hc23, hlam, hphi, u3elo3]
                                      · rcases h5bigk with h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h357, h360, h364, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p374_1, u0elo4]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h0, h287, h366, h370, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p374_1, u2elo1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h323, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h337, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h287, hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h0, h287, h366, h370, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p374_1, u2elo1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h362, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h364, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h290, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h359, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h368, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h370, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h290, h366, h370, hc23, hlam, hphi, p374_1, u3elo4]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h359, h366, h370, hc23, hlam, hphi, p374_1, u3elo4]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h366, h370, hc23, hlam, hphi, p374_1, u3elo4]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h372, hlam, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          rcases p374_3 (m.d 0 5) (by simp) with h395 | h395
                                          · linarith only [h337, h395, hlam]
                                          · rcases p374_3 (m.d 1 5) (by simp) with h397 | h397
                                            · linarith only [h364, h397, hlam]
                                            · rcases p374_3 (m.d 2 5) (by simp) with h399 | h399
                                              · linarith only [h370, h399, hlam]
                                              · rcases p374_3 (m.d 3 5) (by simp) with h401 | h401
                                                · linarith only [h372, h401, hlam]
                                                · linarith only [h323, h401, hlam]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          rcases p374_3 (m.d 0 5) (by simp) with h404 | h404
                                          · linarith only [h337, h404, hlam]
                                          · linarith only [h287, h404, hlam]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          rcases p374_3 (m.d 0 5) (by simp) with h407 | h407
                                          · linarith only [h337, h407, hlam]
                                          · linarith only [h290, h407, hlam]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [h286, h323, h357, hc23, hc45, hlam, hphi, ht34, p374_1]
                                        · have p374_0 := h374c.1
                                          have p374_1 := h374c.2.1
                                          have p374_2 := h374c.2.2.1
                                          have p374_3 := h374c.2.2.2
                                          linarith only [hlam, p374_0]
                        · linarith only [h0, h359, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h286, h357, h358, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h286, h357, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h287, h290, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h416 | h416
            · rcases m.htr 0 3 4 (by decide) (by decide) with h417 | h417
              · linarith only [h0, h286, h289, h417, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h419 | h419
                · rcases m.htr 0 4 5 (by decide) (by decide) with h420 | h420
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h422 | h422
                      · linarith only [h0, h286, h289, h421, h422, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h286, h421, h422, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h421, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h0, h286, h289, h417, h419, h420, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
                      · linarith only [h0, h286, h289, h428, h429, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h286, h428, h429, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h286, h428, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · linarith only [h0, h287, h289, h427, hlam]
            · linarith only [h0, h287, h416, hlam]
        · linarith only [h0, h286, h288, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h436 | h436
        · rcases m.htr 0 2 4 (by decide) (by decide) with h437 | h437
          · rcases m.htr 0 2 5 (by decide) (by decide) with h438 | h438
            · rcases m.htr 0 3 4 (by decide) (by decide) with h439 | h439
              · rcases m.htr 0 3 5 (by decide) (by decide) with h440 | h440
                · linarith only [h286, h287, h440, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                  · linarith only [h286, h287, h439, h442, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                          · linarith only [h286, h447, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h439, h440, h444, h447, hc23, hlam, hphi, u3elo4]
                        · linarith only [h438, h446, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h437, h445, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h286, h444, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h453 | h453
                · linarith only [h286, h287, h453, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h455 | h455
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h456 | h456
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h457 | h457
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h458 | h458
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                          · linarith only [h286, h439, h459, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h461 | h461
                            · linarith only [h286, h287, h453, h458, h461, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h286, h287, h461, hc13, hlam, hphi, u3elo4]
                        · linarith only [h438, h458, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h437, h457, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h286, h456, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h468 | h468
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h469 | h469
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h470 | h470
                          · linarith only [h286, h439, h470, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h472 | h472
                            · linarith only [h286, h287, h469, h472, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h286, h287, h472, hc13, hlam, hphi, u3elo4]
                        · linarith only [h0, h286, h438, h467, h469, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h286, h467, h468, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h286, h467, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h478 | h478
              · rcases m.htr 0 3 5 (by decide) (by decide) with h479 | h479
                · linarith only [h286, h287, h479, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h481 | h481
                  · linarith only [h436, h438, h478, h479, h481, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h484 | h484
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h485 | h485
                        · linarith only [h0, h286, h438, h483, h485, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h286, h483, h485, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h286, h437, h483, h484, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h483, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h490 | h490
                · linarith only [h286, h287, h478, h490, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h492 | h492
                  · linarith only [h437, h438, h492, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h494 | h494
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h495 | h495
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h496 | h496
                        · linarith only [h438, h496, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h286, h494, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h286, h494, h495, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h286, h494, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h501 | h501
            · rcases m.htr 0 3 4 (by decide) (by decide) with h502 | h502
              · linarith only [h0, h286, h437, h502, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h504 | h504
                · linarith only [h286, h287, h502, h504, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h508 | h508
                      · linarith only [h437, h508, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h286, h507, h508, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h286, h507, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · linarith only [h437, h501, h506, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h513 | h513
              · linarith only [h0, h286, h437, h513, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h515 | h515
                · linarith only [h0, h286, h501, h515, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h517 | h517
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h518 | h518
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h519 | h519
                      · linarith only [h0, h286, h437, h518, h519, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h286, h518, h519, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h518, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
                      · linarith only [h0, h286, h437, h523, h524, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h286, h523, h524, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h286, h523, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h286, h436, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h529 | h529
      · rcases m.htr 0 2 3 (by decide) (by decide) with h530 | h530
        · rcases m.htr 0 2 4 (by decide) (by decide) with h531 | h531
          · rcases m.htr 0 2 5 (by decide) (by decide) with h532 | h532
            · rcases m.htr 0 3 4 (by decide) (by decide) with h533 | h533
              · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
                · rcases m.htr 0 4 5 (by decide) (by decide) with h535 | h535
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h536 | h536
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h537 | h537
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h538 | h538
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h539 | h539
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h540 | h540
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h541 | h541
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h542 | h542
                                · linarith only [h530, h542, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h533, h542, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h530, h533, h535, h541, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h286, h540, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h286, h530, h533, h539, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h529, h538, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                      · linarith only [h286, h529, h536, h537, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h529, h536, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h551 | h551
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h552 | h552
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h555 | h555
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h556 | h556
                              · linarith only [h529, h535, h556, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h558 | h558
                                · linarith only [h530, h558, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h530, h533, h558, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h286, h555, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h286, h529, h533, h553, h554, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h0, h553, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h286, h529, h551, h552, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h529, h551, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h286, h529, h534, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h567 | h567
                · rcases m.htr 0 4 5 (by decide) (by decide) with h568 | h568
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h569 | h569
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h570 | h570
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h571 | h571
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h572 | h572
                          · linarith only [h286, h533, h572, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h286, h529, h571, h572, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h571, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h286, h529, h531, h569, h570, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h530, h569, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h286, h529, h533, h568, hlam]
                · linarith only [h286, h529, h567, hlam]
            · linarith only [h286, h529, h530, h532, hc23, hlam, hphi, u3elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h581 | h581
            · rcases m.htr 0 3 4 (by decide) (by decide) with h582 | h582
              · linarith only [h530, h531, h582, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h584 | h584
                · rcases m.htr 0 4 5 (by decide) (by decide) with h585 | h585
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h586 | h586
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h587 | h587
                      · linarith only [h530, h531, h587, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h587, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h529, h530, h586, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h0, h529, h531, h585, hlam]
                · linarith only [h286, h529, h584, hlam]
            · linarith only [h286, h529, h530, h581, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h594 | h594
          · rcases m.htr 0 2 5 (by decide) (by decide) with h595 | h595
            · rcases m.htr 0 3 4 (by decide) (by decide) with h596 | h596
              · rcases m.htr 0 3 5 (by decide) (by decide) with h597 | h597
                · rcases m.htr 0 4 5 (by decide) (by decide) with h598 | h598
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h599 | h599
                    · linarith only [h530, h594, h599, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h599, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h602 | h602
                    · linarith only [h530, h594, h602, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h529, h602, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h0, h529, h530, h597, hlam]
              · linarith only [h530, h594, h596, hlam]
            · linarith only [h0, h529, h595, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h608 | h608
            · rcases m.htr 0 3 4 (by decide) (by decide) with h609 | h609
              · rcases m.htr 0 3 5 (by decide) (by decide) with h610 | h610
                · rcases m.htr 0 4 5 (by decide) (by decide) with h611 | h611
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h612 | h612
                    · linarith only [h0, h530, h612, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h529, h612, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h0, h529, h594, h611, hlam]
                · linarith only [h0, h529, h594, h609, h610, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h617 | h617
                · rcases m.htr 0 4 5 (by decide) (by decide) with h618 | h618
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
                    · linarith only [h0, h529, h530, h619, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h529, h619, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h286, h529, h609, h618, hlam]
                · linarith only [h0, h529, h530, h617, hlam]
            · linarith only [h0, h529, h608, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h625 | h625
        · rcases m.htr 0 2 4 (by decide) (by decide) with h626 | h626
          · rcases m.htr 0 2 5 (by decide) (by decide) with h627 | h627
            · rcases m.htr 0 3 4 (by decide) (by decide) with h628 | h628
              · rcases m.htr 0 3 5 (by decide) (by decide) with h629 | h629
                · rcases m.htr 0 4 5 (by decide) (by decide) with h630 | h630
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h631 | h631
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h632 | h632
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h633 | h633
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h634 | h634
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h635 | h635
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h636 | h636
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h637 | h637
                                · linarith only [h625, h637, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h628, h637, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h630, h636, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h286, h629, h635, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h286, h634, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h627, h633, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h0, h632, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h631, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h646 | h646
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h647 | h647
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h648 | h648
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h649 | h649
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h650 | h650
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h651 | h651
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h652 | h652
                                · linarith only [h625, h652, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h628, h652, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h655 | h655
                                · linarith only [h625, h655, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h625, h628, h655, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h625, h629, h650, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h286, h628, h629, h649, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h627, h648, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h647, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h646, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h663 | h663
                  · linarith only [h628, h629, h663, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h665 | h665
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h666 | h666
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h667 | h667
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h668 | h668
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h669 | h669
                            · linarith only [h628, h629, h665, h669, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h286, h669, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h286, h627, h628, h629, h668, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h627, h667, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h626, h666, hlam]
                    · linarith only [h0, h625, h665, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h676 | h676
                · rcases m.htr 0 4 5 (by decide) (by decide) with h677 | h677
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h678 | h678
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h680 | h680
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h681 | h681
                          · linarith only [h628, h681, hc03, hlam, hphi, u3elo1]
                          · linarith only [h286, h681, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h627, h680, hlam]
                      · linarith only [h0, h626, h679, hlam]
                    · linarith only [h0, h625, h678, hlam]
                  · linarith only [h628, h676, h677, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h688 | h688
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h689 | h689
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h690 | h690
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h691 | h691
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h692 | h692
                          · linarith only [h628, h692, hc03, hlam, hphi, u3elo1]
                          · linarith only [h286, h692, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h627, h691, hlam]
                      · linarith only [h0, h626, h690, hlam]
                    · linarith only [h0, h625, h689, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h698 | h698
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h699 | h699
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h700 | h700
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h701 | h701
                          · linarith only [h286, h628, h701, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h286, h701, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h627, h700, hlam]
                      · linarith only [h0, h626, h699, hlam]
                    · linarith only [h0, h625, h698, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h707 | h707
              · rcases m.htr 0 3 5 (by decide) (by decide) with h708 | h708
                · linarith only [h625, h627, h708, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h710 | h710
                  · linarith only [h625, h627, h707, h710, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h712 | h712
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h713 | h713
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h714 | h714
                        · linarith only [h627, h714, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h714, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h286, h626, h712, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h625, h627, h712, hc01, hlam, hphi, ht12, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h719 | h719
                · linarith only [h626, h627, h707, h719, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h721 | h721
                  · linarith only [h626, h627, h721, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h723 | h723
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h724 | h724
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h725 | h725
                        · linarith only [h627, h725, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h725, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h286, h626, h723, h724, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h723, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h730 | h730
            · rcases m.htr 0 3 4 (by decide) (by decide) with h731 | h731
              · linarith only [h625, h626, h731, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h733 | h733
                · rcases m.htr 0 4 5 (by decide) (by decide) with h734 | h734
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h735 | h735
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h736 | h736
                      · linarith only [h626, h736, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h736, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h625, h735, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h625, h626, h731, h733, h734, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h741 | h741
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h742 | h742
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h743 | h743
                      · linarith only [h625, h626, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h743, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h625, h742, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h626, h730, h741, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h748 | h748
              · linarith only [h625, h626, h748, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h750 | h750
                · linarith only [h625, h730, h750, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h752 | h752
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h753 | h753
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h754 | h754
                      · linarith only [h626, h754, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h754, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h625, h753, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h758 | h758
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h759 | h759
                      · linarith only [h626, h759, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h759, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h625, h758, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h763 | h763
          · rcases m.htr 0 2 5 (by decide) (by decide) with h764 | h764
            · rcases m.htr 0 3 4 (by decide) (by decide) with h765 | h765
              · rcases m.htr 0 3 5 (by decide) (by decide) with h766 | h766
                · rcases m.htr 0 4 5 (by decide) (by decide) with h767 | h767
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h768 | h768
                    · linarith only [h625, h768, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h768, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h771 | h771
                    · linarith only [h625, h763, h771, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h771, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h625, h764, h766, hlam]
              · linarith only [h625, h763, h765, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h776 | h776
              · rcases m.htr 0 3 5 (by decide) (by decide) with h777 | h777
                · rcases m.htr 0 4 5 (by decide) (by decide) with h778 | h778
                  · linarith only [h763, h764, h778, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h780 | h780
                    · linarith only [h625, h780, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h780, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h783 | h783
                  · linarith only [h625, h763, h777, h783, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h785 | h785
                    · linarith only [h625, h763, h785, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h785, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h625, h763, h776, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h789 | h789
            · rcases m.htr 0 3 4 (by decide) (by decide) with h790 | h790
              · rcases m.htr 0 3 5 (by decide) (by decide) with h791 | h791
                · rcases m.htr 0 4 5 (by decide) (by decide) with h792 | h792
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h793 | h793
                    · linarith only [h625, h793, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h793, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h763, h789, h792, hlam]
                · linarith only [h763, h789, h790, h791, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h798 | h798
                · rcases m.htr 0 4 5 (by decide) (by decide) with h799 | h799
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h800 | h800
                    · linarith only [h625, h789, h800, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h800, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h625, h789, h790, h799, hlam]
                · linarith only [h625, h789, h798, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h805 | h805
              · rcases m.htr 0 3 5 (by decide) (by decide) with h806 | h806
                · rcases m.htr 0 4 5 (by decide) (by decide) with h807 | h807
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h808 | h808
                    · linarith only [h625, h808, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h808, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h811 | h811
                    · linarith only [h0, h625, h811, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h811, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h814 | h814
                  · linarith only [h805, h806, h814, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h816 | h816
                    · linarith only [h0, h625, h816, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h816, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h819 | h819
                · rcases m.htr 0 4 5 (by decide) (by decide) with h820 | h820
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h821 | h821
                    · linarith only [h0, h625, h821, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h821, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h805, h819, h820, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h825 | h825
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h826 | h826
                    · linarith only [h0, h625, h826, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h826, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h829 | h829
                    · linarith only [h0, h625, h829, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h829, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
