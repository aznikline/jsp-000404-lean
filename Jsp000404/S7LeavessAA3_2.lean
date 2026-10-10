import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAA3_H_I_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 1 5) (by simp) with h8 | h8
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · rcases m.htr 0 1 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h11, h7, hlam]
                  · linarith only [h11, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h10, h5, hlam, p0_1]
              · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
              · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                · rcases m.htr 0 1 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h18, h7, hlam]
                  · linarith only [h18, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h17, h5, hlam, p0_1]
              · linarith only [h16, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h23 | h23
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 4 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h23, h27, hlam]
                    · linarith only [h27, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h26, h7, hlam, p0_1]
                · linarith only [h25, h5, hlam, p0_1]
              · linarith only [h24, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 1 3 (by decide) (by decide) with h34 | h34
                · rcases m.htr 0 1 4 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                        · linarith only [h38, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · linarith only [h38, h5, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                        · linarith only [h41, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · linarith only [h41, h5, hlam]
                    · linarith only [h23, h36, hlam, p0_1]
                  · linarith only [h35, h7, hlam, p0_1]
                · linarith only [h34, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h33, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h49 | h49
    · rcases p0_3 (m.d 1 2) (by simp) with h50 | h50
      · rcases p0_3 (m.d 1 3) (by simp) with h51 | h51
        · linarith only [h51, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
          · rcases p0_3 (m.d 1 5) (by simp) with h54 | h54
            · rcases m.htr 0 1 2 (by decide) (by decide) with h55 | h55
              · linarith only [h50, h55, hlam]
              · linarith only [h55, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
              · linarith only [h50, h58, hlam]
              · linarith only [h58, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h61 | h61
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · linarith only [h50, h62, hlam]
              · linarith only [h62, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h65 | h65
              · linarith only [h50, h65, hlam]
              · linarith only [h65, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h68 | h68
        · linarith only [h68, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
          · rcases p0_3 (m.d 1 5) (by simp) with h71 | h71
            · rcases m.htr 0 1 2 (by decide) (by decide) with h72 | h72
              · rcases m.htr 0 1 3 (by decide) (by decide) with h73 | h73
                · rcases m.htr 0 1 4 (by decide) (by decide) with h74 | h74
                  · linarith only [h70, h74, hlam]
                  · linarith only [h50, h74, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h73, hlam, p0_0]
              · linarith only [h50, h72, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h79 | h79
              · rcases m.htr 0 1 3 (by decide) (by decide) with h80 | h80
                · rcases m.htr 0 1 4 (by decide) (by decide) with h81 | h81
                  · linarith only [h70, h81, hlam]
                  · linarith only [h50, h81, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h80, hlam, p0_0]
              · linarith only [h50, h79, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h86 | h86
            · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
              · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
                    · linarith only [h86, h90, hlam]
                    · linarith only [h50, h90, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h70, h89, hlam, p0_1]
                · linarith only [h88, hlam, p0_0]
              · linarith only [h50, h87, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h96 | h96
              · rcases m.htr 0 1 3 (by decide) (by decide) with h97 | h97
                · rcases m.htr 0 1 4 (by decide) (by decide) with h98 | h98
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h99 | h99
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                        · linarith only [h101, h50, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                          · linarith only [h101, h103, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                            · linarith only [h101, h105, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                              · linarith only [h107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h107, h70, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
                        · linarith only [h110, h50, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                          · linarith only [h110, h112, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
                            · linarith only [h110, h114, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                              · linarith only [h100, h116, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                              · linarith only [h116, h70, hlam]
                    · linarith only [h86, h99, hlam, p0_1]
                  · linarith only [h98, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h97, hlam, p0_0]
              · linarith only [h96, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
    · linarith only [h49, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h124 | h124
    · rcases p0_3 (m.d 1 2) (by simp) with h125 | h125
      · rcases p0_3 (m.d 1 3) (by simp) with h126 | h126
        · linarith only [h126, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h128 | h128
          · linarith only [h128, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h130 | h130
            · rcases m.htr 0 1 2 (by decide) (by decide) with h131 | h131
              · linarith only [h125, h131, hlam]
              · linarith only [h126, h131, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
              · linarith only [h125, h134, hlam]
              · linarith only [h126, h134, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h137 | h137
        · linarith only [h125, h137, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h139 | h139
          · linarith only [h139, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h141 | h141
            · rcases m.htr 0 1 2 (by decide) (by decide) with h142 | h142
              · rcases m.htr 0 1 3 (by decide) (by decide) with h143 | h143
                · rcases m.htr 0 1 4 (by decide) (by decide) with h144 | h144
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h145 | h145
                    · linarith only [h141, h145, hlam]
                    · linarith only [h125, h145, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h144, hlam, p0_0]
                · linarith only [h137, h143, hlam, p0_1]
              · linarith only [h125, h142, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h151 | h151
              · rcases m.htr 0 1 3 (by decide) (by decide) with h152 | h152
                · rcases m.htr 0 1 4 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                        · linarith only [h125, h156, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h158 | h158
                          · linarith only [h125, h158, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
                            · linarith only [h137, h156, h160, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                              · linarith only [h137, h162, hlam]
                              · linarith only [h155, h156, h162, hc12, hlam, hphi, ht23, u3elo0]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                        · linarith only [h125, h165, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                          · linarith only [h125, h167, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                            · linarith only [h137, h165, h169, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                              · linarith only [h137, h171, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                                · linarith only [h171, h173, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                                  · linarith only [h175, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                  · linarith only [h141, h175, hlam]
                    · linarith only [h154, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h153, hlam, p0_0]
                · linarith only [h152, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h125, h151, hlam, p0_1]
    · linarith only [h124, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h183 | h183
    · rcases p0_3 (m.d 1 2) (by simp) with h184 | h184
      · rcases p0_3 (m.d 1 3) (by simp) with h185 | h185
        · linarith only [h185, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h187 | h187
          · rcases p0_3 (m.d 1 5) (by simp) with h188 | h188
            · linarith only [h188, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h190 | h190
              · linarith only [h184, h190, hlam]
              · linarith only [h185, h190, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h193 | h193
            · linarith only [h193, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h195 | h195
              · linarith only [h184, h195, hlam]
              · linarith only [h185, h195, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h198 | h198
        · linarith only [h184, h198, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
          · rcases p0_3 (m.d 1 5) (by simp) with h201 | h201
            · linarith only [h201, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h203 | h203
              · rcases m.htr 0 1 3 (by decide) (by decide) with h204 | h204
                · rcases m.htr 0 1 4 (by decide) (by decide) with h205 | h205
                  · linarith only [h200, h205, hlam]
                  · linarith only [h184, h205, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h198, h204, hlam, p0_1]
              · linarith only [h184, h203, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h210 | h210
            · linarith only [h210, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 1 3 (by decide) (by decide) with h213 | h213
                · rcases m.htr 0 1 4 (by decide) (by decide) with h214 | h214
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h215 | h215
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h216 | h216
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                        · linarith only [h184, h217, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                          · linarith only [h198, h217, h219, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                            · linarith only [h184, h221, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                              · linarith only [h198, h223, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h216, h217, h223, hc12, hlam, hphi, ht23, u3elo0]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
                        · linarith only [h184, h226, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
                          · linarith only [h198, h226, h228, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h230 | h230
                            · linarith only [h184, h230, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                              · linarith only [h198, h216, h232, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h234 | h234
                                · linarith only [h198, h234, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
                                  · linarith only [h200, h236, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h238 | h238
                                    · linarith only [h213, h216, h226, h238, hc12, hlam, hphi, ht23, u3elo2]
                                    · linarith only [h226, h238, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h215, hlam, p0_0]
                  · linarith only [h214, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                · linarith only [h200, h213, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h184, h212, hlam, p0_1]
    · linarith only [h183, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h248 | h248
    · rcases p0_3 (m.d 1 2) (by simp) with h249 | h249
      · rcases p0_3 (m.d 1 3) (by simp) with h250 | h250
        · linarith only [h250, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h252 | h252
          · rcases p0_3 (m.d 1 5) (by simp) with h253 | h253
            · rcases m.htr 0 1 2 (by decide) (by decide) with h254 | h254
              · linarith only [h254, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h248, h254, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h257 | h257
              · linarith only [h257, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h248, h257, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h260 | h260
            · rcases m.htr 0 1 2 (by decide) (by decide) with h261 | h261
              · linarith only [h261, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h248, h261, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h264 | h264
              · linarith only [h264, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h248, h264, hlam]
      · linarith only [h249, hlam, p0_0]
    · linarith only [h248, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h269 | h269
    · rcases p0_3 (m.d 1 2) (by simp) with h270 | h270
      · rcases p0_3 (m.d 1 3) (by simp) with h271 | h271
        · linarith only [h271, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h273 | h273
          · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h275 | h275
            · rcases m.htr 0 1 2 (by decide) (by decide) with h276 | h276
              · linarith only [h271, h276, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h269, h276, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h279 | h279
              · linarith only [h271, h279, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h269, h279, hlam]
      · linarith only [h270, hlam, p0_0]
    · linarith only [h269, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h284 | h284
    · rcases p0_3 (m.d 1 2) (by simp) with h285 | h285
      · rcases p0_3 (m.d 1 3) (by simp) with h286 | h286
        · linarith only [h286, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h288 | h288
          · rcases p0_3 (m.d 1 5) (by simp) with h289 | h289
            · linarith only [h289, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h291 | h291
              · linarith only [h286, h291, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h284, h291, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h294 | h294
            · linarith only [h294, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h296 | h296
              · linarith only [h286, h296, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h284, h296, hlam]
      · linarith only [h285, hlam, p0_0]
    · linarith only [h284, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h307 | h307
    · rcases p0_3 (m.d 1 2) (by simp) with h308 | h308
      · linarith only [h308, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h310 | h310
        · linarith only [h310, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h312 | h312
          · rcases p0_3 (m.d 1 5) (by simp) with h313 | h313
            · rcases m.htr 0 1 2 (by decide) (by decide) with h314 | h314
              · rcases m.htr 0 1 3 (by decide) (by decide) with h315 | h315
                · rcases m.htr 0 1 4 (by decide) (by decide) with h316 | h316
                  · linarith only [h316, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h307, h316, hlam]
                · linarith only [h310, h315, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h307, h314, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h321 | h321
              · rcases m.htr 0 1 3 (by decide) (by decide) with h322 | h322
                · rcases m.htr 0 1 4 (by decide) (by decide) with h323 | h323
                  · linarith only [h323, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h307, h323, hlam]
                · linarith only [h310, h322, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h307, h321, hlam, p0_1]
          · linarith only [h312, hlam, p0_0]
    · linarith only [h307, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h330 | h330
    · rcases p0_3 (m.d 1 2) (by simp) with h331 | h331
      · rcases p0_3 (m.d 1 3) (by simp) with h332 | h332
        · linarith only [h332, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h334 | h334
          · rcases p0_3 (m.d 1 5) (by simp) with h335 | h335
            · rcases m.htr 0 1 2 (by decide) (by decide) with h336 | h336
              · linarith only [h331, h336, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h330, h336, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h339 | h339
              · linarith only [h331, h339, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h330, h339, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h334, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h343 | h343
        · linarith only [h343, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h345 | h345
          · rcases p0_3 (m.d 1 5) (by simp) with h346 | h346
            · rcases m.htr 0 1 2 (by decide) (by decide) with h347 | h347
              · rcases m.htr 0 1 3 (by decide) (by decide) with h348 | h348
                · rcases m.htr 0 1 4 (by decide) (by decide) with h349 | h349
                  · linarith only [h331, h349, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h330, h349, hlam]
                · linarith only [h348, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h330, h331, h347, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h354 | h354
              · rcases m.htr 0 1 3 (by decide) (by decide) with h355 | h355
                · rcases m.htr 0 1 4 (by decide) (by decide) with h356 | h356
                  · linarith only [h331, h356, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h330, h356, hlam]
                · linarith only [h355, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h330, h354, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h345, hlam, p0_0]
    · linarith only [h330, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h364 | h364
    · rcases p0_3 (m.d 1 2) (by simp) with h365 | h365
      · rcases p0_3 (m.d 1 3) (by simp) with h366 | h366
        · linarith only [h366, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h368 | h368
          · rcases p0_3 (m.d 1 5) (by simp) with h369 | h369
            · linarith only [h369, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h371 | h371
              · linarith only [h365, h366, h371, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h364, h366, h371, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h368, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h375 | h375
        · linarith only [h365, h375, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h377 | h377
          · rcases p0_3 (m.d 1 5) (by simp) with h378 | h378
            · linarith only [h378, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h380 | h380
              · rcases m.htr 0 1 3 (by decide) (by decide) with h381 | h381
                · rcases m.htr 0 1 4 (by decide) (by decide) with h382 | h382
                  · linarith only [h365, h382, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h364, h382, hlam]
                · linarith only [h375, h381, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h364, h365, h380, hlam, p0_1]
          · linarith only [h377, hlam, p0_0]
    · linarith only [h364, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h390 | h390
    · rcases p0_3 (m.d 1 2) (by simp) with h391 | h391
      · linarith only [h391, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h393 | h393
        · linarith only [h393, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h395 | h395
          · rcases p0_3 (m.d 1 5) (by simp) with h396 | h396
            · rcases m.htr 0 1 2 (by decide) (by decide) with h397 | h397
              · rcases m.htr 0 1 3 (by decide) (by decide) with h398 | h398
                · rcases m.htr 0 1 4 (by decide) (by decide) with h399 | h399
                  · linarith only [h395, h399, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h390, h399, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h390, h393, h398, hlam, p0_1]
              · linarith only [h390, h397, hlam, p0_1]
            · linarith only [h396, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h405 | h405
            · rcases m.htr 0 1 2 (by decide) (by decide) with h406 | h406
              · rcases m.htr 0 1 3 (by decide) (by decide) with h407 | h407
                · rcases m.htr 0 1 4 (by decide) (by decide) with h408 | h408
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h409 | h409
                    · linarith only [h409, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h390, h409, hlam]
                  · linarith only [h395, h408, hc01, hc15, hlam, hphi, p0_1]
                · linarith only [h390, h393, h407, hlam, p0_1]
              · linarith only [h390, h406, hlam, p0_1]
            · linarith only [h405, hlam, p0_0]
    · linarith only [h390, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h417 | h417
    · rcases p0_3 (m.d 1 2) (by simp) with h418 | h418
      · rcases p0_3 (m.d 1 3) (by simp) with h419 | h419
        · linarith only [h419, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h421 | h421
          · rcases p0_3 (m.d 1 5) (by simp) with h422 | h422
            · rcases m.htr 0 1 2 (by decide) (by decide) with h423 | h423
              · linarith only [h418, h423, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h417, h423, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h422, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h427 | h427
            · rcases m.htr 0 1 2 (by decide) (by decide) with h428 | h428
              · linarith only [h418, h428, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h417, h428, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h427, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h432 | h432
        · linarith only [h432, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h434 | h434
          · rcases p0_3 (m.d 1 5) (by simp) with h435 | h435
            · rcases m.htr 0 1 2 (by decide) (by decide) with h436 | h436
              · rcases m.htr 0 1 3 (by decide) (by decide) with h437 | h437
                · rcases m.htr 0 1 4 (by decide) (by decide) with h438 | h438
                  · linarith only [h418, h434, h438, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h417, h418, h438, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h417, h437, hlam, p0_1]
              · linarith only [h417, h418, h436, hlam, p0_1]
            · linarith only [h435, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h444 | h444
            · rcases m.htr 0 1 2 (by decide) (by decide) with h445 | h445
              · rcases m.htr 0 1 3 (by decide) (by decide) with h446 | h446
                · rcases m.htr 0 1 4 (by decide) (by decide) with h447 | h447
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h448 | h448
                    · linarith only [h418, h448, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h417, h448, hlam]
                  · linarith only [h434, h447, hc01, hc15, hlam, hphi, p0_1]
                · linarith only [h417, h446, hlam, p0_1]
              · linarith only [h417, h418, h445, hlam, p0_1]
            · linarith only [h444, hlam, p0_0]
    · linarith only [h417, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h456 | h456
    · rcases p0_3 (m.d 1 2) (by simp) with h457 | h457
      · rcases p0_3 (m.d 1 3) (by simp) with h458 | h458
        · linarith only [h458, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h460 | h460
          · linarith only [h460, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h462 | h462
            · rcases m.htr 0 1 2 (by decide) (by decide) with h463 | h463
              · linarith only [h457, h458, h463, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h456, h458, h463, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h462, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h467 | h467
        · linarith only [h457, h467, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h469 | h469
          · linarith only [h469, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h471 | h471
            · rcases m.htr 0 1 2 (by decide) (by decide) with h472 | h472
              · rcases m.htr 0 1 3 (by decide) (by decide) with h473 | h473
                · rcases m.htr 0 1 4 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h475 | h475
                    · linarith only [h457, h475, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h456, h475, hlam]
                  · linarith only [h474, hc01, hc15, hlam, hphi, p0_1]
                · linarith only [h456, h467, h473, hlam, p0_1]
              · linarith only [h456, h457, h472, hlam, p0_1]
            · linarith only [h471, hlam, p0_0]
    · linarith only [h456, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_I_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
                · linarith only [h5, h9, hlam]
                · linarith only [h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h8, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h13 | h13
              · rcases m.htr 0 1 3 (by decide) (by decide) with h14 | h14
                · linarith only [h14, h5, hlam]
                · linarith only [h14, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h13, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h18 | h18
            · rcases m.htr 0 1 2 (by decide) (by decide) with h19 | h19
              · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
                · linarith only [h20, h5, hlam]
                · linarith only [h20, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h19, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                · linarith only [h25, h5, hlam]
                · linarith only [h25, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h24, hlam, p0_0]
        · linarith only [h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · rcases p0_3 (m.d 1 2) (by simp) with h33 | h33
      · rcases p0_3 (m.d 1 3) (by simp) with h34 | h34
        · rcases p0_3 (m.d 1 4) (by simp) with h35 | h35
          · linarith only [h35, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h37 | h37
            · rcases m.htr 0 1 2 (by decide) (by decide) with h38 | h38
              · linarith only [h33, h38, hlam]
              · linarith only [h38, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h41 | h41
              · linarith only [h33, h41, hlam]
              · linarith only [h41, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h34, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h45 | h45
        · rcases p0_3 (m.d 1 4) (by simp) with h46 | h46
          · linarith only [h46, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h48 | h48
            · rcases m.htr 0 1 2 (by decide) (by decide) with h49 | h49
              · rcases m.htr 0 1 3 (by decide) (by decide) with h50 | h50
                · linarith only [h45, h50, hlam]
                · linarith only [h33, h50, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h33, h49, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · rcases m.htr 0 1 3 (by decide) (by decide) with h55 | h55
                · linarith only [h45, h55, hlam]
                · linarith only [h33, h55, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h33, h54, hlam, p0_1]
        · linarith only [h45, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
    · linarith only [h32, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h61 | h61
    · rcases p0_3 (m.d 1 2) (by simp) with h62 | h62
      · rcases p0_3 (m.d 1 3) (by simp) with h63 | h63
        · rcases p0_3 (m.d 1 4) (by simp) with h64 | h64
          · rcases p0_3 (m.d 1 5) (by simp) with h65 | h65
            · linarith only [h65, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h67 | h67
              · linarith only [h62, h67, hlam]
              · linarith only [h67, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h70 | h70
            · linarith only [h70, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h72 | h72
              · linarith only [h62, h72, hlam]
              · linarith only [h64, h72, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h63, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h76 | h76
        · rcases p0_3 (m.d 1 4) (by simp) with h77 | h77
          · rcases p0_3 (m.d 1 5) (by simp) with h78 | h78
            · linarith only [h78, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h80 | h80
              · rcases m.htr 0 1 3 (by decide) (by decide) with h81 | h81
                · linarith only [h76, h81, hlam]
                · linarith only [h62, h81, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h62, h80, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h85 | h85
            · linarith only [h85, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
              · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                · linarith only [h76, h88, hlam]
                · linarith only [h62, h88, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h62, h87, hlam, p0_1]
        · linarith only [h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
    · linarith only [h61, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h97 | h97
    · rcases p0_3 (m.d 1 2) (by simp) with h98 | h98
      · rcases p0_3 (m.d 1 3) (by simp) with h99 | h99
        · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
          · linarith only [h100, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h102 | h102
            · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
              · linarith only [h103, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h103, h97, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
              · linarith only [h106, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h106, h97, hlam]
        · linarith only [h99, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
      · linarith only [h98, hlam, p0_0]
    · linarith only [h97, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h112 | h112
    · rcases p0_3 (m.d 1 2) (by simp) with h113 | h113
      · rcases p0_3 (m.d 1 3) (by simp) with h114 | h114
        · rcases p0_3 (m.d 1 4) (by simp) with h115 | h115
          · rcases p0_3 (m.d 1 5) (by simp) with h116 | h116
            · linarith only [h116, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · linarith only [h118, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h112, h118, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h121 | h121
            · linarith only [h121, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h123 | h123
              · linarith only [h115, h123, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h112, h123, hlam]
        · linarith only [h114, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
      · linarith only [h113, hlam, p0_0]
    · linarith only [h112, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h130 | h130
    · rcases p0_3 (m.d 1 2) (by simp) with h131 | h131
      · linarith only [h131, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h133 | h133
        · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
          · rcases p0_3 (m.d 1 5) (by simp) with h135 | h135
            · rcases m.htr 0 1 2 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 1 3 (by decide) (by decide) with h137 | h137
                · linarith only [h137, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h130, h137, hlam]
              · linarith only [h136, hc01, hc13, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · rcases m.htr 0 1 3 (by decide) (by decide) with h142 | h142
                · linarith only [h142, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h130, h142, hlam]
              · linarith only [h141, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h146 | h146
            · rcases m.htr 0 1 2 (by decide) (by decide) with h147 | h147
              · rcases m.htr 0 1 3 (by decide) (by decide) with h148 | h148
                · linarith only [h148, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h130, h148, hlam]
              · linarith only [h147, hc01, hc13, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h152 | h152
              · rcases m.htr 0 1 3 (by decide) (by decide) with h153 | h153
                · linarith only [h153, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h130, h153, hlam]
              · linarith only [h152, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h133, hlam, p0_0]
    · linarith only [h130, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 2) (by simp) with h161 | h161
      · rcases p0_3 (m.d 1 3) (by simp) with h162 | h162
        · rcases p0_3 (m.d 1 4) (by simp) with h163 | h163
          · linarith only [h163, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h165 | h165
            · rcases m.htr 0 1 2 (by decide) (by decide) with h166 | h166
              · linarith only [h161, h166, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h160, h166, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h169 | h169
              · linarith only [h161, h169, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h160, h169, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h162, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h173 | h173
        · rcases p0_3 (m.d 1 4) (by simp) with h174 | h174
          · linarith only [h174, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h176 | h176
            · rcases m.htr 0 1 2 (by decide) (by decide) with h177 | h177
              · rcases m.htr 0 1 3 (by decide) (by decide) with h178 | h178
                · linarith only [h161, h178, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h160, h178, hlam]
              · linarith only [h161, h177, hc01, hc13, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h182 | h182
              · rcases m.htr 0 1 3 (by decide) (by decide) with h183 | h183
                · linarith only [h161, h183, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h160, h183, hlam]
              · linarith only [h161, h182, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h173, hlam, p0_0]
    · linarith only [h160, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h189 | h189
    · rcases p0_3 (m.d 1 2) (by simp) with h190 | h190
      · rcases p0_3 (m.d 1 3) (by simp) with h191 | h191
        · rcases p0_3 (m.d 1 4) (by simp) with h192 | h192
          · rcases p0_3 (m.d 1 5) (by simp) with h193 | h193
            · linarith only [h193, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h195 | h195
              · linarith only [h190, h195, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h189, h195, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h198 | h198
            · linarith only [h198, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
              · linarith only [h190, h192, h200, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h189, h192, h200, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h191, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h204 | h204
        · rcases p0_3 (m.d 1 4) (by simp) with h205 | h205
          · rcases p0_3 (m.d 1 5) (by simp) with h206 | h206
            · linarith only [h206, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h208 | h208
              · rcases m.htr 0 1 3 (by decide) (by decide) with h209 | h209
                · linarith only [h190, h209, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h189, h209, hlam]
              · linarith only [h190, h208, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h213 | h213
            · linarith only [h213, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h215 | h215
              · rcases m.htr 0 1 3 (by decide) (by decide) with h216 | h216
                · linarith only [h190, h216, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h189, h216, hlam]
              · linarith only [h190, h215, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h204, hlam, p0_0]
    · linarith only [h189, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h223 | h223
    · rcases p0_3 (m.d 1 2) (by simp) with h224 | h224
      · linarith only [h224, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h226 | h226
        · rcases p0_3 (m.d 1 4) (by simp) with h227 | h227
          · rcases p0_3 (m.d 1 5) (by simp) with h228 | h228
            · rcases m.htr 0 1 2 (by decide) (by decide) with h229 | h229
              · rcases m.htr 0 1 3 (by decide) (by decide) with h230 | h230
                · linarith only [h226, h230, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h223, h230, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h223, h229, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
              · rcases m.htr 0 1 3 (by decide) (by decide) with h235 | h235
                · linarith only [h226, h235, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h223, h235, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h223, h234, hlam, p0_1]
          · linarith only [h227, hlam, p0_0]
        · linarith only [h223, h226, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
    · linarith only [h223, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h244 | h244
    · rcases p0_3 (m.d 1 2) (by simp) with h245 | h245
      · rcases p0_3 (m.d 1 3) (by simp) with h246 | h246
        · rcases p0_3 (m.d 1 4) (by simp) with h247 | h247
          · rcases p0_3 (m.d 1 5) (by simp) with h248 | h248
            · linarith only [h248, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h250 | h250
              · linarith only [h245, h250, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h244, h250, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · linarith only [h247, hlam, p0_0]
        · linarith only [h244, h246, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h255 | h255
        · rcases p0_3 (m.d 1 4) (by simp) with h256 | h256
          · rcases p0_3 (m.d 1 5) (by simp) with h257 | h257
            · linarith only [h257, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h259 | h259
              · rcases m.htr 0 1 3 (by decide) (by decide) with h260 | h260
                · linarith only [h245, h255, h260, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h244, h245, h260, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h244, h245, h259, hlam, p0_1]
          · linarith only [h256, hlam, p0_0]
        · linarith only [h244, h255, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
    · linarith only [h244, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 2) (by simp) with h269 | h269
      · linarith only [h269, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h271 | h271
        · rcases p0_3 (m.d 1 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 1 5) (by simp) with h273 | h273
            · rcases m.htr 0 1 2 (by decide) (by decide) with h274 | h274
              · rcases m.htr 0 1 3 (by decide) (by decide) with h275 | h275
                · linarith only [h271, h275, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h268, h275, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h268, h274, hlam, p0_1]
            · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h280 | h280
            · rcases m.htr 0 1 2 (by decide) (by decide) with h281 | h281
              · rcases m.htr 0 1 3 (by decide) (by decide) with h282 | h282
                · linarith only [h271, h282, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h268, h282, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h268, h281, hlam, p0_1]
            · linarith only [h280, hlam, p0_0]
        · linarith only [h268, h271, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
    · linarith only [h268, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h290 | h290
    · rcases p0_3 (m.d 1 2) (by simp) with h291 | h291
      · rcases p0_3 (m.d 1 3) (by simp) with h292 | h292
        · rcases p0_3 (m.d 1 4) (by simp) with h293 | h293
          · linarith only [h293, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h295 | h295
            · rcases m.htr 0 1 2 (by decide) (by decide) with h296 | h296
              · linarith only [h291, h296, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h290, h296, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h295, hlam, p0_0]
        · linarith only [h290, h292, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h301 | h301
        · rcases p0_3 (m.d 1 4) (by simp) with h302 | h302
          · linarith only [h302, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h304 | h304
            · rcases m.htr 0 1 2 (by decide) (by decide) with h305 | h305
              · rcases m.htr 0 1 3 (by decide) (by decide) with h306 | h306
                · linarith only [h291, h301, h306, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h290, h291, h306, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h290, h291, h305, hlam, p0_1]
            · linarith only [h304, hlam, p0_0]
        · linarith only [h290, h301, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
    · linarith only [h290, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_I_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc13, hlam, hphi, p0_1, u1ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · linarith only [h7, hc14, hlam, hphi, p0_1, u1ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h9 | h9
            · linarith only [h9, hc15, hlam, hphi, p0_1, u1ehi1]
            · rcases h3bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h13 | h13
                · rcases p11_3 (m.d 1 3) (by simp) with h14 | h14
                  · linarith only [h14, hlam, p11_0]
                  · rcases p11_3 (m.d 2 3) (by simp) with h16 | h16
                    · linarith only [h16, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                    · rcases p11_3 (m.d 3 4) (by simp) with h18 | h18
                      · linarith only [h18, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                      · rcases p11_3 (m.d 3 5) (by simp) with h20 | h20
                        · linarith only [h20, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h22 | h22
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h23 | h23
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h25 | h25
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h27 | h27
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                                                      · linarith only [h30, h36, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                      · linarith only [h22, h26, h33, h36, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                                                      · linarith only [h30, h39, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                      · linarith only [h22, h26, h33, h39, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                  · linarith only [h20, h34, hlam]
                                                · linarith only [h18, h33, hlam]
                                              · linarith only [h32, h9, hlam]
                                            · linarith only [h31, h7, hlam]
                                          · linarith only [h16, h30, hlam]
                                        · linarith only [h29, hc13, hc35, hlam, hphi, p11_1]
                                      · linarith only [h28, hc13, hc34, hlam, hphi, p11_1]
                                    · linarith only [h26, h27, hc24, hlam, hphi, ht12, p11_1, u1ehi2]
                                  · linarith only [h16, h22, h26, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi1]
                                · linarith only [h23, h25, hc15, hlam, hphi, p11_1, u1ehi2]
                              · linarith only [h23, h24, hc14, hlam, hphi, p11_1, u1ehi2]
                            · linarith only [h23, hlam, p11_0]
                          · linarith only [h22, hlam, p0_0]
                · linarith only [h13, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h56 | h56
                · rcases p11_3 (m.d 1 3) (by simp) with h57 | h57
                  · linarith only [h5, h57, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · rcases p11_3 (m.d 2 3) (by simp) with h59 | h59
                    · linarith only [h59, hlam, p11_0]
                    · rcases p11_3 (m.d 3 4) (by simp) with h61 | h61
                      · linarith only [h57, h61, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                      · rcases p11_3 (m.d 3 5) (by simp) with h63 | h63
                        · linarith only [h57, h63, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h65 | h65
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h66 | h66
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h67 | h67
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h68 | h68
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h69 | h69
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h70 | h70
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h71 | h71
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h72 | h72
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
                                          · linarith only [h57, h73, hlam]
                                          · linarith only [h5, h73, hlam]
                                        · linarith only [h63, h72, hlam, p11_1]
                                      · linarith only [h61, h71, hlam, p11_1]
                                    · linarith only [h57, h69, h70, hc24, hlam, hphi, ht12, p11_1, u1ehi2]
                                  · linarith only [h69, hlam, p11_0]
                                · linarith only [h68, h9, hlam, p0_1]
                              · linarith only [h67, h7, hlam, p0_1]
                            · linarith only [h57, h66, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                          · linarith only [h65, hlam, p0_0]
                · linarith only [h56, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h85 | h85
                · rcases p11_3 (m.d 1 3) (by simp) with h86 | h86
                  · linarith only [h5, h86, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · rcases p11_3 (m.d 2 3) (by simp) with h88 | h88
                    · linarith only [h86, h88, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                    · rcases p11_3 (m.d 3 4) (by simp) with h90 | h90
                      · linarith only [h90, hlam, p11_0]
                      · rcases p11_3 (m.d 3 5) (by simp) with h92 | h92
                        · linarith only [h86, h92, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h94 | h94
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h95 | h95
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h96 | h96
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h97 | h97
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h98 | h98
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h99 | h99
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h101 | h101
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                                                · linarith only [h105, h86, hlam]
                                                · linarith only [h105, h94, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                              · linarith only [h104, h9, hlam]
                                            · linarith only [h103, h7, hlam]
                                          · linarith only [h102, h5, hlam]
                                        · linarith only [h101, h92, hlam, p11_1]
                                      · linarith only [h100, hlam, p11_0]
                                    · linarith only [h86, h98, h99, hc24, hlam, hphi, ht12, p11_1, u1ehi2]
                                  · linarith only [h88, h94, h95, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi1]
                                · linarith only [h97, hc15, hlam, hphi, p0_1, u1ehi1]
                              · linarith only [h86, h95, h96, hc14, hlam, hphi, p11_1, u1ehi2]
                            · linarith only [h86, h95, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                          · linarith only [h94, hlam, p0_0]
                · linarith only [h85, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h120 | h120
                · rcases p11_3 (m.d 1 3) (by simp) with h121 | h121
                  · linarith only [h121, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · rcases p11_3 (m.d 2 3) (by simp) with h123 | h123
                    · linarith only [h121, h123, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                    · rcases p11_3 (m.d 3 4) (by simp) with h125 | h125
                      · linarith only [h121, h125, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                      · rcases p11_3 (m.d 3 5) (by simp) with h127 | h127
                        · linarith only [h127, hlam, p11_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h129 | h129
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h130 | h130
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h131 | h131
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h132 | h132
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h133 | h133
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h134 | h134
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h135 | h135
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h136 | h136
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h141 | h141
                                                  · linarith only [h121, h141, hlam]
                                                  · linarith only [h129, h133, h140, h141, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi3]
                                                · linarith only [h125, h129, h133, h140, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                              · linarith only [h139, h9, hlam]
                                            · linarith only [h138, h7, hlam]
                                          · linarith only [h137, h5, hlam]
                                        · linarith only [h136, hlam, p11_0]
                                      · linarith only [h125, h135, hlam, p11_1]
                                    · linarith only [h121, h133, h134, hc24, hlam, hphi, ht12, p11_1, u1ehi2]
                                  · linarith only [h123, h129, h133, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi1]
                                · linarith only [h132, hc15, hlam, hphi, p0_1, u1ehi1]
                              · linarith only [h121, h130, h131, hc14, hlam, hphi, p11_1, u1ehi2]
                            · linarith only [h121, h130, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                          · linarith only [h129, hlam, p0_0]
                · linarith only [h120, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h162 | h162
                · linarith only [h162, hlam, p11_0]
                · rcases p11_3 (m.d 1 3) (by simp) with h164 | h164
                  · linarith only [h164, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h164, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc23, hlam, hphi, ht12, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h169 | h169
                · rcases p11_3 (m.d 1 3) (by simp) with h170 | h170
                  · linarith only [h170, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h170, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                · rcases p11_3 (m.d 1 3) (by simp) with h173 | h173
                  · linarith only [h169, h173, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h173, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h176 | h176
                · rcases p11_3 (m.d 1 3) (by simp) with h177 | h177
                  · linarith only [h177, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h177, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                · rcases p11_3 (m.d 1 3) (by simp) with h180 | h180
                  · linarith only [h176, h180, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h180, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h183 | h183
                · linarith only [h183, hlam, p11_0]
                · rcases p11_3 (m.d 1 3) (by simp) with h185 | h185
                  · linarith only [h185, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h185, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h189 | h189
                · rcases p11_3 (m.d 1 3) (by simp) with h190 | h190
                  · linarith only [h190, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h190, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · rcases p11_3 (m.d 1 3) (by simp) with h193 | h193
                  · linarith only [h189, h193, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h193, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h197 | h197
                · rcases p11_3 (m.d 1 3) (by simp) with h198 | h198
                  · linarith only [h198, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h198, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · rcases p11_3 (m.d 1 3) (by simp) with h201 | h201
                  · linarith only [h197, h201, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h201, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h204 | h204
                · linarith only [h204, hlam, p11_0]
                · rcases p11_3 (m.d 1 3) (by simp) with h206 | h206
                  · linarith only [h206, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h206, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h210 | h210
                · rcases p11_3 (m.d 1 3) (by simp) with h211 | h211
                  · linarith only [h211, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h211, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · rcases p11_3 (m.d 1 3) (by simp) with h214 | h214
                  · linarith only [h210, h214, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h214, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h217 | h217
                · rcases p11_3 (m.d 1 3) (by simp) with h218 | h218
                  · linarith only [h218, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h218, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · rcases p11_3 (m.d 1 3) (by simp) with h221 | h221
                  · linarith only [h217, h221, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h221, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h226 | h226
    · rcases p0_3 (m.d 1 2) (by simp) with h227 | h227
      · linarith only [h227, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h229 | h229
        · linarith only [h229, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h231 | h231
          · linarith only [h231, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h233 | h233
            · linarith only [h233, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases h3bigk with h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hlam, p235_0]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h237 | h237
                · rcases p235_3 (m.d 1 3) (by simp) with h238 | h238
                  · linarith only [h238, hlam, p235_0]
                  · rcases p235_3 (m.d 2 3) (by simp) with h240 | h240
                    · linarith only [h240, hc23, hlam, hphi, ht12, p235_1, u1ehi2]
                    · rcases p235_3 (m.d 3 4) (by simp) with h242 | h242
                      · linarith only [h242, hc34, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
                      · rcases p235_3 (m.d 3 5) (by simp) with h244 | h244
                        · linarith only [h244, hc35, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h246 | h246
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h247 | h247
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h248 | h248
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h249 | h249
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h250 | h250
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h251 | h251
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h253 | h253
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                                          · linarith only [h227, h254, hlam]
                                          · linarith only [h240, h254, hlam]
                                        · linarith only [h244, h253, hlam, p235_1]
                                      · linarith only [h242, h252, hlam, p235_1]
                                    · linarith only [h250, h251, hc24, hlam, hphi, ht12, p235_1, u1ehi2]
                                  · linarith only [h240, h246, h250, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
                                · linarith only [h233, h247, h249, hlam, p235_1]
                              · linarith only [h231, h247, h248, hlam, p235_1]
                            · linarith only [h247, hlam, p0_0]
                          · linarith only [h246, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h237, hlam, p235_0]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h266 | h266
                · rcases p235_3 (m.d 1 3) (by simp) with h267 | h267
                  · linarith only [h267, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · rcases p235_3 (m.d 2 3) (by simp) with h269 | h269
                    · linarith only [h269, hlam, p235_0]
                    · rcases p235_3 (m.d 3 4) (by simp) with h271 | h271
                      · linarith only [h227, h267, h271, hc34, hlam, hphi, ht12, ht23, p235_1, u1ehi1]
                      · rcases p235_3 (m.d 3 5) (by simp) with h273 | h273
                        · linarith only [h227, h267, h273, hc35, hlam, hphi, ht12, ht23, p235_1, u1ehi1]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h275 | h275
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h276 | h276
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h277 | h277
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h278 | h278
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h279 | h279
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h280 | h280
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h281 | h281
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
                                          · linarith only [h227, h283, hlam]
                                          · linarith only [h275, h279, h283, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p235_1, u1ehi1]
                                        · linarith only [h273, h282, hlam, p235_1]
                                      · linarith only [h271, h281, hlam, p235_1]
                                    · linarith only [h267, h279, h280, hc24, hlam, hphi, ht12, p235_1, u1ehi2]
                                  · linarith only [h279, hlam, p235_0]
                                · linarith only [h233, h267, h276, h278, hlam, p235_1]
                              · linarith only [h231, h267, h276, h277, hlam, p235_1]
                            · linarith only [h276, hlam, p0_0]
                          · linarith only [h275, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h266, hlam, p235_0]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h295 | h295
                · rcases p235_3 (m.d 1 3) (by simp) with h296 | h296
                  · linarith only [h296, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p235_1]
                  · rcases p235_3 (m.d 2 3) (by simp) with h298 | h298
                    · linarith only [h227, h296, h298, hc23, hlam, hphi, ht12, p235_1, u1ehi1]
                    · rcases p235_3 (m.d 3 4) (by simp) with h300 | h300
                      · linarith only [h300, hlam, p235_0]
                      · rcases p235_3 (m.d 3 5) (by simp) with h302 | h302
                        · linarith only [h227, h296, h302, hc35, hlam, hphi, ht12, ht23, p235_1, u1ehi1]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h304 | h304
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h305 | h305
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h306 | h306
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h307 | h307
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h308 | h308
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h310 | h310
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h311 | h311
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h312 | h312
                                          · linarith only [h227, h312, hlam]
                                          · linarith only [h298, h304, h308, h312, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p235_1, u1ehi1]
                                        · linarith only [h302, h311, hlam, p235_1]
                                      · linarith only [h310, hlam, p235_0]
                                    · linarith only [h296, h308, h309, hc24, hlam, hphi, ht12, p235_1, u1ehi2]
                                  · linarith only [h298, h304, h308, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p235_1, u1ehi1]
                                · linarith only [h233, h307, hlam, p0_1]
                              · linarith only [h231, h296, h305, h306, hlam, p235_1]
                            · linarith only [h305, hlam, p0_0]
                          · linarith only [h304, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h295, hlam, p235_0]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h324 | h324
                · rcases p235_3 (m.d 1 3) (by simp) with h325 | h325
                  · linarith only [h325, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p235_1]
                  · rcases p235_3 (m.d 2 3) (by simp) with h327 | h327
                    · linarith only [h227, h325, h327, hc23, hlam, hphi, ht12, p235_1, u1ehi1]
                    · rcases p235_3 (m.d 3 4) (by simp) with h329 | h329
                      · linarith only [h227, h325, h329, hc34, hlam, hphi, ht12, ht23, p235_1, u1ehi1]
                      · rcases p235_3 (m.d 3 5) (by simp) with h331 | h331
                        · linarith only [h331, hlam, p235_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h334 | h334
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h335 | h335
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h336 | h336
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h337 | h337
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h338 | h338
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h339 | h339
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h340 | h340
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                                          · linarith only [h227, h341, hlam]
                                          · linarith only [h327, h337, h341, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p235_1, u1ehi1]
                                        · linarith only [h340, hlam, p235_0]
                                      · linarith only [h329, h339, hlam, p235_1]
                                    · linarith only [h325, h337, h338, hc24, hlam, hphi, ht12, p235_1, u1ehi2]
                                  · linarith only [h327, h333, h334, h337, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p235_1, u1ehi1]
                                · linarith only [h233, h336, hlam, p0_1]
                              · linarith only [h231, h325, h334, h335, hlam, p235_1]
                            · linarith only [h334, hlam, p0_0]
                          · linarith only [h333, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h324, hlam, p235_0]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hlam, p235_0]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p235_1]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p235_1]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h358 | h358
                · linarith only [h358, hlam, p235_0]
                · rcases p235_3 (m.d 1 3) (by simp) with h360 | h360
                  · linarith only [h360, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h227, h360, hc23, hlam, hphi, ht12, p235_1, u1ehi1]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [h231, hc23, hlam, hphi, ht12, p235_1, u1ehi3]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hlam, p235_0]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h365 | h365
                · rcases p235_3 (m.d 1 3) (by simp) with h366 | h366
                  · linarith only [h366, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h227, h366, hc23, hlam, hphi, ht12, p235_1, u1ehi1]
                · rcases p235_3 (m.d 1 3) (by simp) with h369 | h369
                  · linarith only [h365, h369, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h369, hc23, hlam, hphi, ht12, p235_1, u1ehi2]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h372 | h372
                · rcases p235_3 (m.d 1 3) (by simp) with h373 | h373
                  · linarith only [h373, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p235_1]
                  · linarith only [h373, hc23, hlam, hphi, ht12, p235_1, u1ehi2]
                · rcases p235_3 (m.d 1 3) (by simp) with h376 | h376
                  · linarith only [h372, h376, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h376, hc23, hlam, hphi, ht12, p235_1, u1ehi2]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h379 | h379
                · linarith only [h379, hlam, p235_0]
                · rcases p235_3 (m.d 1 3) (by simp) with h381 | h381
                  · linarith only [h381, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h381, hc34, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [h233, hc34, hlam, hphi, ht12, ht23, p235_1, u1ehi4]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h385 | h385
                · rcases p235_3 (m.d 1 3) (by simp) with h386 | h386
                  · linarith only [h386, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h386, hc34, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
                · rcases p235_3 (m.d 1 3) (by simp) with h389 | h389
                  · linarith only [h385, h389, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h389, hc34, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hlam, p235_0]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h393 | h393
                · rcases p235_3 (m.d 1 3) (by simp) with h394 | h394
                  · linarith only [h394, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p235_1]
                  · linarith only [h394, hc34, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
                · rcases p235_3 (m.d 1 3) (by simp) with h397 | h397
                  · linarith only [h393, h397, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h397, hc34, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h400 | h400
                · linarith only [h400, hlam, p235_0]
                · rcases p235_3 (m.d 1 3) (by simp) with h402 | h402
                  · linarith only [h402, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h402, hc35, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h406 | h406
                · rcases p235_3 (m.d 1 3) (by simp) with h407 | h407
                  · linarith only [h407, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h407, hc35, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
                · rcases p235_3 (m.d 1 3) (by simp) with h410 | h410
                  · linarith only [h406, h410, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h410, hc35, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                rcases p235_3 (m.d 0 3) (by simp) with h413 | h413
                · rcases p235_3 (m.d 1 3) (by simp) with h414 | h414
                  · linarith only [h414, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h414, hc35, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
                · rcases p235_3 (m.d 1 3) (by simp) with h417 | h417
                  · linarith only [h413, h417, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p235_1]
                  · linarith only [h417, hc35, hlam, hphi, ht12, ht23, p235_1, u1ehi2]
              · have p235_0 := h235c.1
                have p235_1 := h235c.2.1
                have p235_2 := h235c.2.2.1
                have p235_3 := h235c.2.2.2
                linarith only [hlam, p235_0]
    · linarith only [h226, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h422 | h422
    · rcases p0_3 (m.d 1 2) (by simp) with h423 | h423
      · linarith only [h423, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h425 | h425
        · linarith only [h425, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h427 | h427
          · linarith only [h427, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h429 | h429
            · linarith only [h429, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases h3bigk with h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [hlam, p431_0]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h433 | h433
                · rcases p431_3 (m.d 1 3) (by simp) with h434 | h434
                  · linarith only [h434, hlam, p431_0]
                  · rcases p431_3 (m.d 2 3) (by simp) with h436 | h436
                    · linarith only [h436, hc23, hlam, hphi, ht12, p431_1, u1ehi2]
                    · rcases p431_3 (m.d 3 4) (by simp) with h438 | h438
                      · linarith only [h438, hc34, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                      · rcases p431_3 (m.d 3 5) (by simp) with h440 | h440
                        · linarith only [h440, hc35, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h442 | h442
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h443 | h443
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h444 | h444
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h445 | h445
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h446 | h446
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h447 | h447
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h448 | h448
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h449 | h449
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
                                            · linarith only [h423, h451, hlam]
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                                                · linarith only [h425, h454, hlam]
                                                · linarith only [h438, h454, hlam]
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h457 | h457
                                                · linarith only [h425, h457, hlam]
                                                · linarith only [h438, h457, hlam]
                                          · linarith only [h436, h450, hlam]
                                        · linarith only [h440, h449, hlam, p431_1]
                                      · linarith only [h438, h448, hlam, p431_1]
                                    · linarith only [h446, h447, hc24, hlam, hphi, ht12, p431_1, u1ehi2]
                                  · linarith only [h436, h442, h446, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi1]
                                · linarith only [h429, h443, h445, hc14, hlam, hphi, p431_1, u1ehi2]
                              · linarith only [h444, hlam, p0_0]
                            · linarith only [h443, hlam, p431_0]
                          · linarith only [h442, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h433, hlam, p431_0]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h470 | h470
                · rcases p431_3 (m.d 1 3) (by simp) with h471 | h471
                  · linarith only [h425, h471, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · rcases p431_3 (m.d 2 3) (by simp) with h473 | h473
                    · linarith only [h473, hlam, p431_0]
                    · rcases p431_3 (m.d 3 4) (by simp) with h475 | h475
                      · linarith only [h471, h475, hc34, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                      · rcases p431_3 (m.d 3 5) (by simp) with h477 | h477
                        · linarith only [h471, h477, hc35, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h479 | h479
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h480 | h480
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h481 | h481
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h482 | h482
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h483 | h483
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h484 | h484
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h485 | h485
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h486 | h486
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h487 | h487
                                          · linarith only [h471, h487, hlam]
                                          · linarith only [h483, h487, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi1]
                                        · linarith only [h477, h486, hlam, p431_1]
                                      · linarith only [h475, h485, hlam, p431_1]
                                    · linarith only [h471, h483, h484, hc24, hlam, hphi, ht12, p431_1, u1ehi2]
                                  · linarith only [h483, hlam, p431_0]
                                · linarith only [h429, h482, hlam, p0_1]
                              · linarith only [h481, hlam, p0_0]
                            · linarith only [h471, h480, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi0]
                          · linarith only [h479, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h470, hlam, p431_0]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h499 | h499
                · rcases p431_3 (m.d 1 3) (by simp) with h500 | h500
                  · linarith only [h425, h500, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p431_1]
                  · rcases p431_3 (m.d 2 3) (by simp) with h502 | h502
                    · linarith only [h500, h502, hc23, hlam, hphi, ht12, p431_1, u1ehi2]
                    · rcases p431_3 (m.d 3 4) (by simp) with h504 | h504
                      · linarith only [h504, hlam, p431_0]
                      · rcases p431_3 (m.d 3 5) (by simp) with h506 | h506
                        · linarith only [h500, h506, hc35, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h508 | h508
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h509 | h509
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h510 | h510
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h511 | h511
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h512 | h512
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h513 | h513
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h514 | h514
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h515 | h515
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h516 | h516
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h517 | h517
                                            · linarith only [h423, h517, hlam]
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h519 | h519
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h520 | h520
                                                · linarith only [h425, h520, hlam]
                                                · linarith only [h520, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi2]
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h523 | h523
                                                · linarith only [h425, h523, hlam]
                                                · linarith only [h508, h512, h523, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi2]
                                          · linarith only [h502, h508, h512, h516, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi1]
                                        · linarith only [h506, h515, hlam, p431_1]
                                      · linarith only [h514, hlam, p431_0]
                                    · linarith only [h500, h512, h513, hc24, hlam, hphi, ht12, p431_1, u1ehi2]
                                  · linarith only [h502, h508, h512, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi1]
                                · linarith only [h429, h511, hlam, p0_1]
                              · linarith only [h510, hlam, p0_0]
                            · linarith only [h500, h509, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi0]
                          · linarith only [h508, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h499, hlam, p431_0]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h536 | h536
                · rcases p431_3 (m.d 1 3) (by simp) with h537 | h537
                  · linarith only [h425, h537, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p431_1]
                  · rcases p431_3 (m.d 2 3) (by simp) with h539 | h539
                    · linarith only [h537, h539, hc23, hlam, hphi, ht12, p431_1, u1ehi2]
                    · rcases p431_3 (m.d 3 4) (by simp) with h541 | h541
                      · linarith only [h537, h541, hc34, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                      · rcases p431_3 (m.d 3 5) (by simp) with h543 | h543
                        · linarith only [h543, hlam, p431_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h545 | h545
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h546 | h546
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h547 | h547
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h548 | h548
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h549 | h549
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h550 | h550
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h551 | h551
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h552 | h552
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h553 | h553
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h554 | h554
                                            · linarith only [h423, h554, hlam]
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h556 | h556
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h557 | h557
                                                · linarith only [h425, h557, hlam]
                                                · linarith only [h541, h549, h557, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi2]
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
                                                · linarith only [h425, h560, hlam]
                                                · linarith only [h541, h545, h549, h560, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi2]
                                          · linarith only [h539, h545, h549, h553, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi1]
                                        · linarith only [h552, hlam, p431_0]
                                      · linarith only [h541, h551, hlam, p431_1]
                                    · linarith only [h537, h549, h550, hc24, hlam, hphi, ht12, p431_1, u1ehi2]
                                  · linarith only [h539, h545, h549, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p431_1, u1ehi1]
                                · linarith only [h548, hc15, hlam, hphi, p0_1, u1ehi3]
                              · linarith only [h547, hlam, p0_0]
                            · linarith only [h537, h546, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, p431_1, u1ehi3]
                          · linarith only [h545, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h536, hlam, p431_0]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [h425, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [hlam, p431_0]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [h425, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [h425, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p431_1]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [h425, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p431_1]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h578 | h578
                · linarith only [h578, hlam, p431_0]
                · rcases p431_3 (m.d 1 3) (by simp) with h580 | h580
                  · linarith only [h425, h580, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h580, hc23, hlam, hphi, ht12, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [hc23, hlam, hphi, ht12, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [hlam, p431_0]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h585 | h585
                · rcases p431_3 (m.d 1 3) (by simp) with h586 | h586
                  · linarith only [h425, h586, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h586, hc23, hlam, hphi, ht12, p431_1, u1ehi2]
                · rcases p431_3 (m.d 1 3) (by simp) with h589 | h589
                  · linarith only [h425, h585, h589, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h589, hc23, hlam, hphi, ht12, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h592 | h592
                · rcases p431_3 (m.d 1 3) (by simp) with h593 | h593
                  · linarith only [h425, h593, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p431_1]
                  · linarith only [h593, hc23, hlam, hphi, ht12, p431_1, u1ehi2]
                · rcases p431_3 (m.d 1 3) (by simp) with h596 | h596
                  · linarith only [h425, h592, h596, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h596, hc23, hlam, hphi, ht12, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h599 | h599
                · linarith only [h599, hlam, p431_0]
                · rcases p431_3 (m.d 1 3) (by simp) with h601 | h601
                  · linarith only [h425, h601, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h601, hc34, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [hc34, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h605 | h605
                · rcases p431_3 (m.d 1 3) (by simp) with h606 | h606
                  · linarith only [h425, h606, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h606, hc34, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                · rcases p431_3 (m.d 1 3) (by simp) with h609 | h609
                  · linarith only [h425, h605, h609, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h609, hc34, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [hlam, p431_0]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h613 | h613
                · rcases p431_3 (m.d 1 3) (by simp) with h614 | h614
                  · linarith only [h425, h614, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p431_1]
                  · linarith only [h614, hc34, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                · rcases p431_3 (m.d 1 3) (by simp) with h617 | h617
                  · linarith only [h425, h613, h617, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h617, hc34, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h620 | h620
                · linarith only [h620, hlam, p431_0]
                · rcases p431_3 (m.d 1 3) (by simp) with h622 | h622
                  · linarith only [h425, h622, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h622, hc35, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h626 | h626
                · rcases p431_3 (m.d 1 3) (by simp) with h627 | h627
                  · linarith only [h425, h627, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h627, hc35, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                · rcases p431_3 (m.d 1 3) (by simp) with h630 | h630
                  · linarith only [h425, h626, h630, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h630, hc35, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                rcases p431_3 (m.d 0 3) (by simp) with h633 | h633
                · rcases p431_3 (m.d 1 3) (by simp) with h634 | h634
                  · linarith only [h425, h634, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h634, hc35, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
                · rcases p431_3 (m.d 1 3) (by simp) with h637 | h637
                  · linarith only [h425, h633, h637, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p431_1]
                  · linarith only [h637, hc35, hlam, hphi, ht12, ht23, p431_1, u1ehi2]
              · have p431_0 := h431c.1
                have p431_1 := h431c.2.1
                have p431_2 := h431c.2.2.1
                have p431_3 := h431c.2.2.2
                linarith only [hlam, p431_0]
    · linarith only [h422, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h642 | h642
    · rcases p0_3 (m.d 1 2) (by simp) with h643 | h643
      · linarith only [h643, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h645 | h645
        · linarith only [h645, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h647 | h647
          · linarith only [h647, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h649 | h649
            · linarith only [h649, hlam, p0_0]
            · rcases h3bigk with h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [hlam, p651_0]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h653 | h653
                · rcases p651_3 (m.d 1 3) (by simp) with h654 | h654
                  · linarith only [h654, hlam, p651_0]
                  · rcases p651_3 (m.d 2 3) (by simp) with h656 | h656
                    · linarith only [h656, hc23, hlam, hphi, ht12, p651_1, u1ehi2]
                    · rcases p651_3 (m.d 3 4) (by simp) with h658 | h658
                      · linarith only [h658, hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                      · rcases p651_3 (m.d 3 5) (by simp) with h660 | h660
                        · linarith only [h660, hc35, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h662 | h662
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h663 | h663
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h664 | h664
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h665 | h665
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h666 | h666
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h667 | h667
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h668 | h668
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h669 | h669
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h670 | h670
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h671 | h671
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h672 | h672
                                              · linarith only [h643, h672, hlam]
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h674 | h674
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h675 | h675
                                                  · linarith only [h645, h675, hlam]
                                                  · linarith only [h660, h675, hlam]
                                                · linarith only [h658, h674, hlam]
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h679 | h679
                                              · linarith only [h643, h679, hlam]
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h681 | h681
                                                · linarith only [h670, h671, h681, hlam]
                                                · linarith only [h658, h681, hlam]
                                          · linarith only [h656, h670, hlam]
                                        · linarith only [h660, h669, hlam, p651_1]
                                      · linarith only [h668, hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                                    · linarith only [h666, h667, hc24, hlam, hphi, ht12, p651_1, u1ehi2]
                                  · linarith only [h656, h662, h666, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi1]
                                · linarith only [h665, hlam, p0_0]
                              · linarith only [h663, h664, hc14, hlam, hphi, p651_1, u1ehi2]
                            · linarith only [h663, hlam, p651_0]
                          · linarith only [h647, h662, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h653, hlam, p651_0]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h694 | h694
                · rcases p651_3 (m.d 1 3) (by simp) with h695 | h695
                  · linarith only [h645, h695, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · rcases p651_3 (m.d 2 3) (by simp) with h697 | h697
                    · linarith only [h697, hlam, p651_0]
                    · rcases p651_3 (m.d 3 4) (by simp) with h699 | h699
                      · linarith only [h695, h699, hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                      · rcases p651_3 (m.d 3 5) (by simp) with h701 | h701
                        · linarith only [h695, h701, hc35, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h703 | h703
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h704 | h704
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h705 | h705
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h706 | h706
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h707 | h707
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h708 | h708
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h709 | h709
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h710 | h710
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h711 | h711
                                          · linarith only [h695, h711, hlam]
                                          · linarith only [h707, h711, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi1]
                                        · linarith only [h701, h710, hlam, p651_1]
                                      · linarith only [h699, h709, hlam, p651_1]
                                    · linarith only [h695, h707, h708, hc24, hlam, hphi, ht12, p651_1, u1ehi2]
                                  · linarith only [h707, hlam, p651_0]
                                · linarith only [h706, hlam, p0_0]
                              · linarith only [h647, h705, hlam, p0_1]
                            · linarith only [h695, h704, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi0]
                          · linarith only [h647, h703, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h694, hlam, p651_0]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h723 | h723
                · rcases p651_3 (m.d 1 3) (by simp) with h724 | h724
                  · linarith only [h645, h724, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p651_1]
                  · rcases p651_3 (m.d 2 3) (by simp) with h726 | h726
                    · linarith only [h724, h726, hc23, hlam, hphi, ht12, p651_1, u1ehi2]
                    · rcases p651_3 (m.d 3 4) (by simp) with h728 | h728
                      · linarith only [h728, hlam, p651_0]
                      · rcases p651_3 (m.d 3 5) (by simp) with h730 | h730
                        · linarith only [h724, h730, hc35, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h732 | h732
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h733 | h733
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h734 | h734
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h735 | h735
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h736 | h736
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h737 | h737
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h738 | h738
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h739 | h739
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h741 | h741
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h742 | h742
                                              · linarith only [h643, h742, hlam]
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h744 | h744
                                                · linarith only [h724, h744, hlam]
                                                · linarith only [h736, h744, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi2]
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h747 | h747
                                              · linarith only [h643, h747, hlam]
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h749 | h749
                                                · linarith only [h724, h749, hlam]
                                                · linarith only [h732, h736, h749, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi2]
                                          · linarith only [h726, h732, h736, h740, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi1]
                                        · linarith only [h730, h739, hlam, p651_1]
                                      · linarith only [h738, hlam, p651_0]
                                    · linarith only [h724, h736, h737, hc24, hlam, hphi, ht12, p651_1, u1ehi2]
                                  · linarith only [h726, h732, h733, h736, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi1]
                                · linarith only [h735, hlam, p0_0]
                              · linarith only [h724, h733, h734, hc14, hlam, hphi, p651_1, u1ehi2]
                            · linarith only [h724, h733, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, p651_1, u1ehi4]
                          · linarith only [h732, hc12, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h723, hlam, p651_0]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h762 | h762
                · rcases p651_3 (m.d 1 3) (by simp) with h763 | h763
                  · linarith only [h645, h763, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p651_1]
                  · rcases p651_3 (m.d 2 3) (by simp) with h765 | h765
                    · linarith only [h763, h765, hc23, hlam, hphi, ht12, p651_1, u1ehi2]
                    · rcases p651_3 (m.d 3 4) (by simp) with h767 | h767
                      · linarith only [h763, h767, hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                      · rcases p651_3 (m.d 3 5) (by simp) with h769 | h769
                        · linarith only [h769, hlam, p651_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h771 | h771
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h772 | h772
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h773 | h773
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h774 | h774
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h775 | h775
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h776 | h776
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h777 | h777
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h778 | h778
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h779 | h779
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h780 | h780
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h781 | h781
                                              · linarith only [h643, h781, hlam]
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h784 | h784
                                                  · linarith only [h645, h784, hlam]
                                                  · linarith only [h771, h775, h783, h784, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi3]
                                                · linarith only [h767, h771, h775, h783, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi2]
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h788 | h788
                                              · linarith only [h643, h788, hlam]
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h790 | h790
                                                · linarith only [h779, h780, h790, hlam]
                                                · linarith only [h767, h771, h775, h790, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi2]
                                          · linarith only [h765, h771, h775, h779, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi1]
                                        · linarith only [h778, hlam, p651_0]
                                      · linarith only [h767, h777, hlam, p651_1]
                                    · linarith only [h763, h775, h776, hc24, hlam, hphi, ht12, p651_1, u1ehi2]
                                  · linarith only [h765, h771, h775, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1, u1ehi1]
                                · linarith only [h774, hlam, p0_0]
                              · linarith only [h773, hc14, hlam, hphi, p0_1, u1ehi4]
                            · linarith only [h763, h772, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, p651_1, u1ehi4]
                          · linarith only [h771, hc12, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h762, hlam, p651_0]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [h645, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [hlam, p651_0]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [h645, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [h645, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p651_1]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [h645, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p651_1]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h808 | h808
                · linarith only [h808, hlam, p651_0]
                · rcases p651_3 (m.d 1 3) (by simp) with h810 | h810
                  · linarith only [h645, h810, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h810, hc23, hlam, hphi, ht12, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [hc23, hlam, hphi, ht12, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [hlam, p651_0]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h815 | h815
                · rcases p651_3 (m.d 1 3) (by simp) with h816 | h816
                  · linarith only [h645, h816, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h816, hc23, hlam, hphi, ht12, p651_1, u1ehi2]
                · rcases p651_3 (m.d 1 3) (by simp) with h819 | h819
                  · linarith only [h645, h815, h819, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h819, hc23, hlam, hphi, ht12, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h822 | h822
                · rcases p651_3 (m.d 1 3) (by simp) with h823 | h823
                  · linarith only [h645, h823, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p651_1]
                  · linarith only [h823, hc23, hlam, hphi, ht12, p651_1, u1ehi2]
                · rcases p651_3 (m.d 1 3) (by simp) with h826 | h826
                  · linarith only [h645, h822, h826, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h826, hc23, hlam, hphi, ht12, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h829 | h829
                · linarith only [h829, hlam, p651_0]
                · rcases p651_3 (m.d 1 3) (by simp) with h831 | h831
                  · linarith only [h645, h831, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h831, hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h835 | h835
                · rcases p651_3 (m.d 1 3) (by simp) with h836 | h836
                  · linarith only [h645, h836, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h836, hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                · rcases p651_3 (m.d 1 3) (by simp) with h839 | h839
                  · linarith only [h645, h835, h839, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h839, hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [hlam, p651_0]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h843 | h843
                · rcases p651_3 (m.d 1 3) (by simp) with h844 | h844
                  · linarith only [h645, h844, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p651_1]
                  · linarith only [h844, hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                · rcases p651_3 (m.d 1 3) (by simp) with h847 | h847
                  · linarith only [h645, h843, h847, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h847, hc34, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h850 | h850
                · linarith only [h850, hlam, p651_0]
                · rcases p651_3 (m.d 1 3) (by simp) with h852 | h852
                  · linarith only [h645, h852, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h852, hc35, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h856 | h856
                · rcases p651_3 (m.d 1 3) (by simp) with h857 | h857
                  · linarith only [h645, h857, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h857, hc35, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                · rcases p651_3 (m.d 1 3) (by simp) with h860 | h860
                  · linarith only [h645, h856, h860, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h860, hc35, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                rcases p651_3 (m.d 0 3) (by simp) with h863 | h863
                · rcases p651_3 (m.d 1 3) (by simp) with h864 | h864
                  · linarith only [h645, h864, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h864, hc35, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
                · rcases p651_3 (m.d 1 3) (by simp) with h867 | h867
                  · linarith only [h645, h863, h867, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p651_1]
                  · linarith only [h867, hc35, hlam, hphi, ht12, ht23, p651_1, u1ehi2]
              · have p651_0 := h651c.1
                have p651_1 := h651c.2.1
                have p651_2 := h651c.2.2.1
                have p651_3 := h651c.2.2.2
                linarith only [hlam, p651_0]
    · linarith only [h642, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_I_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.2.1
  have h3ehi := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · linarith only [h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h8, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · linarith only [h11, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h11, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · linarith only [h15, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h15, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h18 | h18
              · linarith only [h18, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h18, hlam, p0_0]
        · linarith only [h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h24 | h24
    · rcases p0_3 (m.d 0 2) (by simp) with h25 | h25
      · rcases p0_3 (m.d 0 3) (by simp) with h26 | h26
        · rcases p0_3 (m.d 0 4) (by simp) with h27 | h27
          · linarith only [h27, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · rcases m.htr 0 1 2 (by decide) (by decide) with h30 | h30
              · linarith only [h25, h30, hlam]
              · linarith only [h30, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · linarith only [h25, h33, hlam]
              · linarith only [h33, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h26, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h37 | h37
        · rcases p0_3 (m.d 0 4) (by simp) with h38 | h38
          · linarith only [h38, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
            · rcases m.htr 0 1 2 (by decide) (by decide) with h41 | h41
              · linarith only [h25, h41, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h25, h41, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h44 | h44
              · linarith only [h25, h44, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h25, h44, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
        · linarith only [h37, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h24, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h49 | h49
    · rcases p0_3 (m.d 0 2) (by simp) with h50 | h50
      · rcases p0_3 (m.d 0 3) (by simp) with h51 | h51
        · rcases p0_3 (m.d 0 4) (by simp) with h52 | h52
          · rcases p0_3 (m.d 0 5) (by simp) with h53 | h53
            · linarith only [h53, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h55 | h55
              · linarith only [h50, h55, hlam]
              · linarith only [h55, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h58 | h58
            · linarith only [h58, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h60 | h60
              · linarith only [h50, h60, hlam]
              · linarith only [h52, h60, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h51, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h64 | h64
        · rcases p0_3 (m.d 0 4) (by simp) with h65 | h65
          · rcases p0_3 (m.d 0 5) (by simp) with h66 | h66
            · linarith only [h66, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h68 | h68
              · linarith only [h50, h68, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h50, h68, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h71 | h71
            · linarith only [h71, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h73 | h73
              · linarith only [h50, h73, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h50, h73, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
        · linarith only [h64, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h49, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h81 | h81
    · rcases p0_3 (m.d 0 2) (by simp) with h82 | h82
      · rcases p0_3 (m.d 0 3) (by simp) with h83 | h83
        · rcases p0_3 (m.d 0 4) (by simp) with h84 | h84
          · linarith only [h84, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h86 | h86
            · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
              · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
                  · linarith only [h87, h89, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h87, h89, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h87, h88, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h81, h87, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h94 | h94
              · rcases m.htr 0 1 3 (by decide) (by decide) with h95 | h95
                · rcases m.htr 0 1 4 (by decide) (by decide) with h96 | h96
                  · linarith only [h94, h96, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h94, h96, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h94, h95, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h81, h94, hlam]
        · linarith only [h83, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h82, hlam, p0_0]
    · linarith only [h81, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h104 | h104
    · rcases p0_3 (m.d 0 2) (by simp) with h105 | h105
      · rcases p0_3 (m.d 0 3) (by simp) with h106 | h106
        · rcases p0_3 (m.d 0 4) (by simp) with h107 | h107
          · rcases p0_3 (m.d 0 5) (by simp) with h108 | h108
            · linarith only [h108, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h110 | h110
              · rcases m.htr 0 1 3 (by decide) (by decide) with h111 | h111
                · rcases m.htr 0 1 4 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h113 | h113
                    · linarith only [h110, h113, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
                    · linarith only [h110, h113, hc05, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h110, h112, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                · linarith only [h110, h111, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1]
              · linarith only [h104, h110, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h119 | h119
            · linarith only [h119, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · rcases m.htr 0 1 3 (by decide) (by decide) with h122 | h122
                · rcases m.htr 0 1 4 (by decide) (by decide) with h123 | h123
                  · linarith only [h107, h121, h123, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h107, h121, h123, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h107, h121, h122, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h104, h121, hlam]
        · linarith only [h106, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h105, hlam, p0_0]
    · linarith only [h104, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h132 | h132
    · rcases p0_3 (m.d 0 2) (by simp) with h133 | h133
      · linarith only [h133, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h135 | h135
        · rcases p0_3 (m.d 0 4) (by simp) with h136 | h136
          · rcases p0_3 (m.d 0 5) (by simp) with h137 | h137
            · rcases m.htr 0 1 2 (by decide) (by decide) with h138 | h138
              · linarith only [h138, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h132, h138, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · linarith only [h132, h141, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h132, h141, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h144 | h144
            · rcases m.htr 0 1 2 (by decide) (by decide) with h145 | h145
              · linarith only [h145, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h132, h145, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h148 | h148
              · linarith only [h148, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h132, h148, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
        · linarith only [h135, hlam, p0_0]
    · linarith only [h132, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h154 | h154
    · rcases p0_3 (m.d 0 2) (by simp) with h155 | h155
      · rcases p0_3 (m.d 0 3) (by simp) with h156 | h156
        · rcases p0_3 (m.d 0 4) (by simp) with h157 | h157
          · linarith only [h157, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h159 | h159
            · rcases m.htr 0 1 2 (by decide) (by decide) with h160 | h160
              · rcases m.htr 0 1 3 (by decide) (by decide) with h161 | h161
                · rcases m.htr 0 1 4 (by decide) (by decide) with h162 | h162
                  · linarith only [h155, h160, h162, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h155, h160, h162, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h154, h161, hlam]
              · linarith only [h154, h160, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h167 | h167
              · rcases m.htr 0 1 3 (by decide) (by decide) with h168 | h168
                · rcases m.htr 0 1 4 (by decide) (by decide) with h169 | h169
                  · linarith only [h155, h167, h169, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h155, h167, h169, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h154, h168, hlam]
              · linarith only [h154, h167, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h156, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h175 | h175
        · rcases p0_3 (m.d 0 4) (by simp) with h176 | h176
          · linarith only [h176, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h178 | h178
            · rcases m.htr 0 1 2 (by decide) (by decide) with h179 | h179
              · linarith only [h154, h155, h179, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h154, h155, h179, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h182 | h182
              · linarith only [h154, h155, h182, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h154, h155, h182, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
        · linarith only [h175, hlam, p0_0]
    · linarith only [h154, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h187 | h187
    · rcases p0_3 (m.d 0 2) (by simp) with h188 | h188
      · rcases p0_3 (m.d 0 3) (by simp) with h189 | h189
        · rcases p0_3 (m.d 0 4) (by simp) with h190 | h190
          · rcases p0_3 (m.d 0 5) (by simp) with h191 | h191
            · linarith only [h191, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h193 | h193
              · rcases m.htr 0 1 3 (by decide) (by decide) with h194 | h194
                · rcases m.htr 0 1 4 (by decide) (by decide) with h195 | h195
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h196 | h196
                    · linarith only [h188, h193, h196, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
                    · linarith only [h188, h193, h196, hc05, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h188, h193, h195, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                · linarith only [h187, h194, hlam]
              · linarith only [h187, h193, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h202 | h202
            · linarith only [h202, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h204 | h204
              · rcases m.htr 0 1 3 (by decide) (by decide) with h205 | h205
                · rcases m.htr 0 1 4 (by decide) (by decide) with h206 | h206
                  · linarith only [h188, h190, h204, h206, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h188, h190, h204, h206, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h187, h205, hlam]
              · linarith only [h187, h190, h204, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h189, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h212 | h212
        · rcases p0_3 (m.d 0 4) (by simp) with h213 | h213
          · rcases p0_3 (m.d 0 5) (by simp) with h214 | h214
            · linarith only [h214, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h216 | h216
              · linarith only [h187, h188, h216, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h187, h188, h216, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h219 | h219
            · linarith only [h219, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h221 | h221
              · linarith only [h188, h221, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h187, h188, h221, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
        · linarith only [h212, hlam, p0_0]
    · linarith only [h187, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h227 | h227
    · rcases p0_3 (m.d 0 2) (by simp) with h228 | h228
      · linarith only [h228, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h230 | h230
        · rcases p0_3 (m.d 0 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 0 5) (by simp) with h232 | h232
            · rcases m.htr 0 1 2 (by decide) (by decide) with h233 | h233
              · linarith only [h233, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h227, h233, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h236 | h236
              · linarith only [h236, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h227, h236, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h231, hlam, p0_0]
        · linarith only [h227, h230, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h227, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h244 | h244
    · rcases p0_3 (m.d 0 2) (by simp) with h245 | h245
      · rcases p0_3 (m.d 0 3) (by simp) with h246 | h246
        · rcases p0_3 (m.d 0 4) (by simp) with h247 | h247
          · rcases p0_3 (m.d 0 5) (by simp) with h248 | h248
            · linarith only [h248, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h250 | h250
              · rcases m.htr 0 1 3 (by decide) (by decide) with h251 | h251
                · rcases m.htr 0 1 4 (by decide) (by decide) with h252 | h252
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h253 | h253
                    · linarith only [h245, h250, h253, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
                    · linarith only [h245, h250, h253, hc05, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h244, h252, hlam]
                · linarith only [h245, h250, h251, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1]
              · linarith only [h244, h250, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · linarith only [h247, hlam, p0_0]
        · linarith only [h244, h246, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h261 | h261
        · rcases p0_3 (m.d 0 4) (by simp) with h262 | h262
          · rcases p0_3 (m.d 0 5) (by simp) with h263 | h263
            · linarith only [h263, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h265 | h265
              · linarith only [h244, h245, h265, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h244, h245, h265, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h262, hlam, p0_0]
        · linarith only [h244, h261, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h244, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h272 | h272
    · rcases p0_3 (m.d 0 2) (by simp) with h273 | h273
      · linarith only [h273, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h275 | h275
        · rcases p0_3 (m.d 0 4) (by simp) with h276 | h276
          · rcases p0_3 (m.d 0 5) (by simp) with h277 | h277
            · rcases m.htr 0 1 2 (by decide) (by decide) with h278 | h278
              · linarith only [h278, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h272, h278, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h277, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h282 | h282
            · rcases m.htr 0 1 2 (by decide) (by decide) with h283 | h283
              · linarith only [h272, h283, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h272, h283, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h282, hlam, p0_0]
        · linarith only [h272, h275, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h272, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h290 | h290
    · rcases p0_3 (m.d 0 2) (by simp) with h291 | h291
      · rcases p0_3 (m.d 0 3) (by simp) with h292 | h292
        · rcases p0_3 (m.d 0 4) (by simp) with h293 | h293
          · linarith only [h293, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
            · rcases m.htr 0 1 2 (by decide) (by decide) with h296 | h296
              · rcases m.htr 0 1 3 (by decide) (by decide) with h297 | h297
                · rcases m.htr 0 1 4 (by decide) (by decide) with h298 | h298
                  · linarith only [h291, h296, h298, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h291, h296, h298, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h291, h296, h297, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h290, h296, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h295, hlam, p0_0]
        · linarith only [h290, h292, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h305 | h305
        · rcases p0_3 (m.d 0 4) (by simp) with h306 | h306
          · linarith only [h306, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h308 | h308
            · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
              · linarith only [h290, h291, h309, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h290, h291, h309, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h308, hlam, p0_0]
        · linarith only [h290, h305, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h290, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_R_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h10, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h13, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, h7, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                      · linarith only [h0, h2, h20, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h17, h22, h4, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                          · rcases h1bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h17, h19, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h17, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h4, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h17, h19, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h17, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h1, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h4, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h7, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h17, hlam, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h5, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h17, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h6, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h19, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                          · linarith only [h19, h24, h4, h7, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                      · linarith only [h4, h52, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                        · linarith only [h17, h4, h54, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                          · linarith only [h19, h4, h56, h7, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h4, h56, h7, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h3, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
              · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                · linarith only [h4, h5, h61, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                  · linarith only [h61, h63, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                      · linarith only [h0, h2, h61, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h4, h5, h66, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h4, h5, h65, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h3, h4, h60, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
              · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                      · linarith only [h0, h2, h4, h71, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h4, h71, h73, h76, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                      · linarith only [h0, h2, h4, h71, h79, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h4, h73, h75, h79, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h73, h74, hc35, hlam, hphi, u3ehi3]
                · linarith only [h4, h71, h73, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                    · linarith only [h71, h72, h86, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                      · linarith only [h0, h2, h4, h71, h88, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h4, h71, h84, h88, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h84, h85, hc35, hlam, hphi, u3ehi3]
                · linarith only [h4, h71, h84, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
              · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h0, h2, h4, h93, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h4, h94, h98, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h4, h94, h97, hlam]
                    · linarith only [h71, h93, h96, hlam]
                  · linarith only [h94, h95, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h94, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h104, h4, h93, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                          · rcases h1bigk with h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [hlam, p113_0]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              rcases p113_3 (m.d 0 1) (by simp) with h115 | h115
                              · rcases p113_3 (m.d 1 2) (by simp) with h116 | h116
                                · linarith only [h116, hlam, p113_0]
                                · rcases p113_3 (m.d 1 3) (by simp) with h118 | h118
                                  · linarith only [h1, h118, hlam]
                                  · linarith only [h118, h4, hlam]
                              · linarith only [h115, hlam, p113_0]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h107, h112, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u3ehi4]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h107, h112, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u3ehi4]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h108, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u3ehi4]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h0, hlam, p113_0]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [hlam, p113_0]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h4, hlam, p113_1]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h71, hlam, p113_1]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h93, hlam, p113_1]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h1, hlam, p113_0]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p113_1]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [hlam, p113_0]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h107, h112, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p113_1, u3ehi4]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h0, h108, h2, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u3ehi4]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p113_1]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h71, hc12, hc24, hlam, hphi, p113_1]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h107, hlam, p113_1]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [hlam, p113_0]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h0, h107, h108, h2, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1, u3ehi4]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p113_1]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h93, hc12, hc25, hlam, hphi, p113_1]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h108, hlam, p113_0]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [h109, hlam, p113_0]
                            · have p113_0 := h113c.1
                              have p113_1 := h113c.2.1
                              have p113_2 := h113c.2.2.1
                              have p113_3 := h113c.2.2.2
                              linarith only [hlam, p113_0]
                          · linarith only [h0, h107, h109, h112, h2, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h107, h111, h4, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h107, h110, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h150 | h150
                          · linarith only [h1, h107, h109, h150, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h1bigk with h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [hlam, p152_0]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              rcases p152_3 (m.d 0 1) (by simp) with h154 | h154
                              · rcases p152_3 (m.d 1 2) (by simp) with h155 | h155
                                · linarith only [h155, hlam, p152_0]
                                · rcases p152_3 (m.d 1 3) (by simp) with h157 | h157
                                  · linarith only [h1, h157, hlam]
                                  · linarith only [h157, h4, hlam]
                              · linarith only [h154, hlam, p152_0]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1, u3ehi1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h107, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1, u3ehi3]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h107, h109, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1, u3ehi3]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h0, hlam, p152_0]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [hlam, p152_0]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h4, hlam, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h71, hlam, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h93, hlam, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h1, hlam, p152_0]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [hlam, p152_0]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h0, h107, h2, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1, u3ehi3]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h0, h107, h109, h2, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1, u3ehi3]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h109, hc12, hc45, hlam, hphi, ht23, ht34, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h107, hlam, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [hlam, p152_0]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h109, hlam, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h0, h149, h2, h93, hlam, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h0, h149, h2, h93, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h108, hlam, p152_0]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [h0, h149, h2, h93, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p152_1]
                            · have p152_0 := h152c.1
                              have p152_1 := h152c.2.1
                              have p152_2 := h152c.2.2.1
                              have p152_3 := h152c.2.2.2
                              linarith only [hlam, p152_0]
                        · linarith only [h107, h149, h4, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h107, h148, h4, hlam]
                  · linarith only [h107, h108, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                  · linarith only [h107, h187, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                      · linarith only [h0, h107, h190, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                        · linarith only [h187, h190, h192, hc34, hlam, hphi, u3ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                          · rcases h1bigk with h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [hlam, p195_0]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              rcases p195_3 (m.d 0 1) (by simp) with h197 | h197
                              · rcases p195_3 (m.d 1 2) (by simp) with h198 | h198
                                · linarith only [h198, hlam, p195_0]
                                · rcases p195_3 (m.d 1 3) (by simp) with h200 | h200
                                  · linarith only [h1, h200, hlam]
                                  · linarith only [h200, h4, hlam]
                              · linarith only [h197, hlam, p195_0]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p195_1, u3ehi1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h107, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p195_1, u3ehi1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h187, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p195_1, u3ehi1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h0, hlam, p195_0]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [hlam, p195_0]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h4, hlam, p195_1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h71, hlam, p195_1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h93, hlam, p195_1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h1, hlam, p195_0]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p195_1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [hlam, p195_0]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h107, hlam, p195_0]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h187, hlam, p195_1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p195_1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h71, hc12, hc24, hlam, hphi, p195_1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h107, hc34, hlam, hphi, p195_1, u3ehi1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [hlam, p195_0]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h107, h187, hc34, hlam, hphi, p195_1, u3ehi1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h0, h2, hc15, hlam, hphi, ht01, p195_1, u0ehi2]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h0, h3, h93, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p195_1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h0, h3, h93, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p195_1, u3ehi1]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [h189, hlam, p195_0]
                            · have p195_0 := h195c.1
                              have p195_1 := h195c.2.1
                              have p195_2 := h195c.2.2.1
                              have p195_3 := h195c.2.2.2
                              linarith only [hlam, p195_0]
                          · linarith only [h189, h190, h194, h71, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                      · linarith only [h0, h107, h2, h228, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h230 | h230
                        · linarith only [h228, h230, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h107, h189, h232, hc34, hlam, hphi, u3ehi1]
                          · linarith only [h228, h232, hc45, hlam, hphi, ht34, u3ehi2]
        · linarith only [h3, hc25, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc13, hlam, hphi, ht01, u0ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sAA3_H_R_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc13, hlam, hphi, p0_1, u1ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · linarith only [h7, hc14, hlam, hphi, p0_1, u1ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h9 | h9
            · linarith only [h9, hc15, hlam, hphi, p0_1, u1ehi1]
            · rcases h3bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h13 | h13
                · rcases p11_3 (m.d 1 3) (by simp) with h14 | h14
                  · linarith only [h14, hlam, p11_0]
                  · rcases p11_3 (m.d 2 3) (by simp) with h16 | h16
                    · linarith only [h16, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                    · rcases p11_3 (m.d 3 4) (by simp) with h18 | h18
                      · linarith only [h18, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                      · rcases p11_3 (m.d 3 5) (by simp) with h20 | h20
                        · linarith only [h20, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h22 | h22
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h23 | h23
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h25 | h25
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h26 | h26
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                                      · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                                              · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                                                · linarith only [h28, h33, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                · linarith only [h22, h25, h31, h33, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                              · linarith only [h20, h32, hlam]
                                            · linarith only [h18, h31, hlam]
                                          · linarith only [h30, h9, hlam]
                                        · linarith only [h29, h7, hlam]
                                      · linarith only [h16, h28, hlam]
                                    · linarith only [h27, hc13, hc35, hlam, hphi, p11_1]
                                  · linarith only [h26, hc13, hc34, hlam, hphi, p11_1]
                                · linarith only [h25, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h23, h24, hc14, hlam, hphi, p11_1, u1ehi2]
                            · linarith only [h23, hlam, p11_0]
                          · linarith only [h22, hlam, p0_0]
                · linarith only [h13, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h48 | h48
                · rcases p11_3 (m.d 1 3) (by simp) with h49 | h49
                  · linarith only [h49, h5, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p11_3 (m.d 2 3) (by simp) with h51 | h51
                    · linarith only [h51, hlam, p11_0]
                    · rcases p11_3 (m.d 3 4) (by simp) with h53 | h53
                      · linarith only [h49, h53, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                      · rcases p11_3 (m.d 3 5) (by simp) with h55 | h55
                        · linarith only [h49, h55, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h57 | h57
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h58 | h58
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h59 | h59
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h60 | h60
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h61 | h61
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h62 | h62
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
                                      · linarith only [h49, h63, hlam]
                                      · linarith only [h5, h63, hlam]
                                    · linarith only [h55, h62, hlam, p11_1]
                                  · linarith only [h53, h61, hlam, p11_1]
                                · linarith only [h60, hlam, p11_0]
                              · linarith only [h59, h7, hc12, hlam, hphi, ht01, u0ehi0]
                            · linarith only [h49, h58, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                          · linarith only [h57, hlam, p0_0]
                · linarith only [h48, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h73 | h73
                · rcases p11_3 (m.d 1 3) (by simp) with h74 | h74
                  · linarith only [h5, h74, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · rcases p11_3 (m.d 2 3) (by simp) with h76 | h76
                    · linarith only [h74, h76, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                    · rcases p11_3 (m.d 3 4) (by simp) with h78 | h78
                      · linarith only [h78, hlam, p11_0]
                      · rcases p11_3 (m.d 3 5) (by simp) with h80 | h80
                        · linarith only [h74, h80, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h82 | h82
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h83 | h83
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h84 | h84
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h85 | h85
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h86 | h86
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h87 | h87
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
                                      · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                                            · linarith only [h74, h91, hlam]
                                            · linarith only [h82, h85, h91, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                          · linarith only [h9, h90, hlam]
                                        · linarith only [h7, h89, hlam]
                                      · linarith only [h5, h88, hlam]
                                    · linarith only [h80, h87, hlam, p11_1]
                                  · linarith only [h86, hlam, p11_0]
                                · linarith only [h85, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h74, h83, h84, hc14, hlam, hphi, p11_1, u1ehi2]
                            · linarith only [h74, h83, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                          · linarith only [h82, hlam, p0_0]
                · linarith only [h73, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h104 | h104
                · rcases p11_3 (m.d 1 3) (by simp) with h105 | h105
                  · linarith only [h105, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · rcases p11_3 (m.d 2 3) (by simp) with h107 | h107
                    · linarith only [h105, h107, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                    · rcases p11_3 (m.d 3 4) (by simp) with h109 | h109
                      · linarith only [h105, h109, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                      · rcases p11_3 (m.d 3 5) (by simp) with h111 | h111
                        · linarith only [h111, hlam, p11_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h113 | h113
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h114 | h114
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h115 | h115
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h116 | h116
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h117 | h117
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h118 | h118
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h119 | h119
                                      · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h122 | h122
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h123 | h123
                                              · linarith only [h105, h123, hlam]
                                              · linarith only [h113, h116, h122, h123, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi3]
                                            · linarith only [h109, h113, h116, h122, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                          · linarith only [h121, h9, hlam]
                                        · linarith only [h120, h7, hlam]
                                      · linarith only [h119, h5, hlam]
                                    · linarith only [h118, hlam, p11_0]
                                  · linarith only [h109, h117, hlam, p11_1]
                                · linarith only [h116, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h105, h114, h115, hc14, hlam, hphi, p11_1, u1ehi2]
                            · linarith only [h105, h114, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                          · linarith only [h113, hlam, p0_0]
                · linarith only [h104, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc23, hlam, hphi, ht01, ht12, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc23, hlam, hphi, ht12, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h145 | h145
                · rcases p11_3 (m.d 1 3) (by simp) with h146 | h146
                  · linarith only [h146, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h146, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                · linarith only [h145, hc23, hlam, hphi, ht01, ht12, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h150 | h150
                · rcases p11_3 (m.d 1 3) (by simp) with h151 | h151
                  · linarith only [h151, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h151, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                · linarith only [h150, hc23, hlam, hphi, ht01, ht12, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h157 | h157
                · rcases p11_3 (m.d 1 3) (by simp) with h158 | h158
                  · linarith only [h158, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h158, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · linarith only [h157, hc34, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h163 | h163
                · rcases p11_3 (m.d 1 3) (by simp) with h164 | h164
                  · linarith only [h164, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h164, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · linarith only [h163, hc34, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h170 | h170
                · rcases p11_3 (m.d 1 3) (by simp) with h171 | h171
                  · linarith only [h171, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h171, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · linarith only [h170, hc35, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h175 | h175
                · rcases p11_3 (m.d 1 3) (by simp) with h176 | h176
                  · linarith only [h176, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h176, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · linarith only [h175, hc35, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h182 | h182
    · rcases p0_3 (m.d 1 2) (by simp) with h183 | h183
      · linarith only [h183, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h185 | h185
        · linarith only [h185, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h187 | h187
          · linarith only [h187, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h189 | h189
            · linarith only [h189, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases h3bigk with h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hlam, p191_0]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h193 | h193
                · rcases p191_3 (m.d 1 3) (by simp) with h194 | h194
                  · linarith only [h194, hlam, p191_0]
                  · rcases p191_3 (m.d 2 3) (by simp) with h196 | h196
                    · linarith only [h196, hc23, hlam, hphi, ht12, p191_1, u1ehi2]
                    · rcases p191_3 (m.d 3 4) (by simp) with h198 | h198
                      · linarith only [h198, hc34, hlam, hphi, ht12, ht23, p191_1, u1ehi2]
                      · rcases p191_3 (m.d 3 5) (by simp) with h200 | h200
                        · linarith only [h200, hc35, hlam, hphi, ht12, ht23, p191_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h202 | h202
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h203 | h203
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h204 | h204
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h205 | h205
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h206 | h206
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h207 | h207
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
                                      · linarith only [h183, h208, hlam]
                                      · linarith only [h196, h208, hlam]
                                    · linarith only [h200, h207, hlam, p191_1]
                                  · linarith only [h198, h206, hlam, p191_1]
                                · linarith only [h196, h205, hc03, hlam, hphi, p191_1, u0ehi1]
                              · linarith only [h187, h203, h204, hlam, p191_1]
                            · linarith only [h203, hlam, p0_0]
                          · linarith only [h183, h202, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p191_1, u1ehi0]
                · linarith only [h193, hlam, p191_0]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h218 | h218
                · rcases p191_3 (m.d 1 3) (by simp) with h219 | h219
                  · linarith only [h219, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p191_3 (m.d 2 3) (by simp) with h221 | h221
                    · linarith only [h221, hlam, p191_0]
                    · rcases p191_3 (m.d 3 4) (by simp) with h223 | h223
                      · linarith only [h183, h219, h223, hc34, hlam, hphi, ht12, ht23, p191_1, u1ehi1]
                      · rcases p191_3 (m.d 3 5) (by simp) with h225 | h225
                        · linarith only [h183, h219, h225, hc35, hlam, hphi, ht12, ht23, p191_1, u1ehi1]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h227 | h227
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h228 | h228
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h229 | h229
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h231 | h231
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h232 | h232
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h233 | h233
                                      · linarith only [h183, h233, hlam]
                                      · linarith only [h230, h233, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p191_1, u1ehi1]
                                    · linarith only [h225, h232, hlam, p191_1]
                                  · linarith only [h223, h231, hlam, p191_1]
                                · linarith only [h230, hlam, p191_0]
                              · linarith only [h187, h229, hc13, hlam, hphi, ht01, u0ehi0]
                            · linarith only [h228, hlam, p0_0]
                          · linarith only [h227, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h218, hlam, p191_0]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h243 | h243
                · rcases p191_3 (m.d 1 3) (by simp) with h244 | h244
                  · linarith only [h244, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p191_3 (m.d 2 3) (by simp) with h246 | h246
                    · linarith only [h183, h244, h246, hc23, hlam, hphi, ht12, p191_1, u1ehi1]
                    · rcases p191_3 (m.d 3 4) (by simp) with h248 | h248
                      · linarith only [h248, hlam, p191_0]
                      · rcases p191_3 (m.d 3 5) (by simp) with h250 | h250
                        · linarith only [h183, h244, h250, hc35, hlam, hphi, ht12, ht23, p191_1, u1ehi1]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h252 | h252
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h253 | h253
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h254 | h254
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h255 | h255
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h256 | h256
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h257 | h257
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                                      · linarith only [h183, h258, hlam]
                                      · linarith only [h246, h252, h255, h258, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p191_1, u1ehi1]
                                    · linarith only [h250, h257, hlam, p191_1]
                                  · linarith only [h256, hlam, p191_0]
                                · linarith only [h246, h255, hc03, hlam, hphi, p191_1, u0ehi1]
                              · linarith only [h187, h244, h253, h254, hlam, p191_1]
                            · linarith only [h253, hlam, p0_0]
                          · linarith only [h252, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h243, hlam, p191_0]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h268 | h268
                · rcases p191_3 (m.d 1 3) (by simp) with h269 | h269
                  · linarith only [h269, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p191_3 (m.d 2 3) (by simp) with h271 | h271
                    · linarith only [h183, h269, h271, hc23, hlam, hphi, ht12, p191_1, u1ehi1]
                    · rcases p191_3 (m.d 3 4) (by simp) with h273 | h273
                      · linarith only [h187, h269, h273, hc34, hlam, hphi, ht12, ht23, p191_1, u1ehi3]
                      · rcases p191_3 (m.d 3 5) (by simp) with h275 | h275
                        · linarith only [h275, hlam, p191_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h277 | h277
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h278 | h278
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h279 | h279
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h280 | h280
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h281 | h281
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
                                      · linarith only [h183, h283, hlam]
                                      · linarith only [h271, h277, h280, h283, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p191_1, u1ehi1]
                                    · linarith only [h282, hlam, p191_0]
                                  · linarith only [h273, h281, hlam, p191_1]
                                · linarith only [h271, h280, hc03, hlam, hphi, p191_1, u0ehi1]
                              · linarith only [h187, h269, h278, h279, hlam, p191_1]
                            · linarith only [h278, hlam, p0_0]
                          · linarith only [h277, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h268, hlam, p191_0]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p191_1]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hlam, p191_0]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p191_1]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p191_1]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p191_1]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hc23, hlam, hphi, ht01, ht12, p191_1, u0ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [h183, hc23, hlam, hphi, ht12, p191_1, u1ehi1]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hlam, p191_0]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h301 | h301
                · rcases p191_3 (m.d 1 3) (by simp) with h302 | h302
                  · linarith only [h302, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p191_1]
                  · linarith only [h302, hc23, hlam, hphi, ht12, p191_1, u1ehi2]
                · linarith only [h301, hc23, hlam, hphi, ht01, ht12, p191_1, u0ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h306 | h306
                · rcases p191_3 (m.d 1 3) (by simp) with h307 | h307
                  · linarith only [h307, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p191_1]
                  · linarith only [h307, hc23, hlam, hphi, ht12, p191_1, u1ehi2]
                · linarith only [h306, hc23, hlam, hphi, ht01, ht12, p191_1, u0ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p191_1, u0ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [h189, hc34, hlam, hphi, ht12, ht23, p191_1, u1ehi4]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h313 | h313
                · rcases p191_3 (m.d 1 3) (by simp) with h314 | h314
                  · linarith only [h314, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p191_1]
                  · linarith only [h314, hc34, hlam, hphi, ht12, ht23, p191_1, u1ehi2]
                · linarith only [h313, hc34, hlam, hphi, ht01, ht12, ht23, p191_1, u0ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hlam, p191_0]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h319 | h319
                · rcases p191_3 (m.d 1 3) (by simp) with h320 | h320
                  · linarith only [h320, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p191_1]
                  · linarith only [h320, hc34, hlam, hphi, ht12, ht23, p191_1, u1ehi2]
                · linarith only [h319, hc34, hlam, hphi, ht01, ht12, ht23, p191_1, u0ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p191_1, u0ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p191_1, u1ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h326 | h326
                · rcases p191_3 (m.d 1 3) (by simp) with h327 | h327
                  · linarith only [h327, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p191_1]
                  · linarith only [h327, hc35, hlam, hphi, ht12, ht23, p191_1, u1ehi2]
                · linarith only [h326, hc35, hlam, hphi, ht01, ht12, ht23, p191_1, u0ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                rcases p191_3 (m.d 0 3) (by simp) with h331 | h331
                · rcases p191_3 (m.d 1 3) (by simp) with h332 | h332
                  · linarith only [h332, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p191_1]
                  · linarith only [h332, hc35, hlam, hphi, ht12, ht23, p191_1, u1ehi2]
                · linarith only [h331, hc35, hlam, hphi, ht01, ht12, ht23, p191_1, u0ehi2]
              · have p191_0 := h191c.1
                have p191_1 := h191c.2.1
                have p191_2 := h191c.2.2.1
                have p191_3 := h191c.2.2.2
                linarith only [hlam, p191_0]
    · linarith only [h182, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h338 | h338
    · rcases p0_3 (m.d 1 2) (by simp) with h339 | h339
      · linarith only [h339, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h341 | h341
        · linarith only [h341, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h343 | h343
          · linarith only [h343, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h345 | h345
            · linarith only [h345, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases h3bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h349 | h349
                · rcases p347_3 (m.d 1 3) (by simp) with h350 | h350
                  · linarith only [h350, hlam, p347_0]
                  · rcases p347_3 (m.d 2 3) (by simp) with h352 | h352
                    · linarith only [h352, hc23, hlam, hphi, ht12, p347_1, u1ehi2]
                    · rcases p347_3 (m.d 3 4) (by simp) with h354 | h354
                      · linarith only [h354, hc34, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                      · rcases p347_3 (m.d 3 5) (by simp) with h356 | h356
                        · linarith only [h356, hc35, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h358 | h358
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h359 | h359
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h360 | h360
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h361 | h361
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h363 | h363
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h364 | h364
                                      · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                                        · linarith only [h339, h365, hlam]
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                                            · linarith only [h341, h368, hlam]
                                            · linarith only [h354, h368, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                                            · linarith only [h341, h371, hlam]
                                            · linarith only [h354, h371, hlam]
                                      · linarith only [h352, h364, hlam]
                                    · linarith only [h356, h363, hlam, p347_1]
                                  · linarith only [h354, h362, hlam, p347_1]
                                · linarith only [h361, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h360, hlam, p0_0]
                            · linarith only [h359, hlam, p347_0]
                          · linarith only [h358, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h349, hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h382 | h382
                · rcases p347_3 (m.d 1 3) (by simp) with h383 | h383
                  · linarith only [h341, h383, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p347_3 (m.d 2 3) (by simp) with h385 | h385
                    · linarith only [h385, hlam, p347_0]
                    · rcases p347_3 (m.d 3 4) (by simp) with h387 | h387
                      · linarith only [h383, h387, hc34, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                      · rcases p347_3 (m.d 3 5) (by simp) with h389 | h389
                        · linarith only [h383, h389, hc35, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h391 | h391
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h392 | h392
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h393 | h393
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h394 | h394
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h396 | h396
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h397 | h397
                                      · linarith only [h383, h397, hlam]
                                      · linarith only [h394, h397, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p347_1, u1ehi1]
                                    · linarith only [h389, h396, hlam, p347_1]
                                  · linarith only [h387, h395, hlam, p347_1]
                                · linarith only [h394, hlam, p347_0]
                              · linarith only [h393, hlam, p0_0]
                            · linarith only [h392, hc13, hlam, hphi, ht01, u0ehi0]
                          · linarith only [h339, h391, hlam, p0_1]
                · linarith only [h382, hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h407 | h407
                · rcases p347_3 (m.d 1 3) (by simp) with h408 | h408
                  · linarith only [h341, h408, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p347_3 (m.d 2 3) (by simp) with h410 | h410
                    · linarith only [h408, h410, hc23, hlam, hphi, ht12, p347_1, u1ehi2]
                    · rcases p347_3 (m.d 3 4) (by simp) with h412 | h412
                      · linarith only [h412, hlam, p347_0]
                      · rcases p347_3 (m.d 3 5) (by simp) with h414 | h414
                        · linarith only [h408, h414, hc35, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h416 | h416
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h417 | h417
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h418 | h418
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h419 | h419
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h420 | h420
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h421 | h421
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h422 | h422
                                      · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                                        · linarith only [h339, h423, hlam]
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h426 | h426
                                            · linarith only [h341, h426, hlam]
                                            · linarith only [h419, h426, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p347_1, u1ehi2]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h429 | h429
                                            · linarith only [h341, h429, hlam]
                                            · linarith only [h416, h419, h429, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p347_1, u1ehi2]
                                      · linarith only [h410, h416, h419, h422, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p347_1, u1ehi1]
                                    · linarith only [h414, h421, hlam, p347_1]
                                  · linarith only [h420, hlam, p347_0]
                                · linarith only [h410, h419, hc03, hlam, hphi, p347_1, u0ehi1]
                              · linarith only [h418, hlam, p0_0]
                            · linarith only [h417, hc13, hlam, hphi, ht01, u0ehi0]
                          · linarith only [h339, h416, hlam, p0_1]
                · linarith only [h407, hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h440 | h440
                · rcases p347_3 (m.d 1 3) (by simp) with h441 | h441
                  · linarith only [h341, h441, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p347_3 (m.d 2 3) (by simp) with h443 | h443
                    · linarith only [h441, h443, hc23, hlam, hphi, ht12, p347_1, u1ehi2]
                    · rcases p347_3 (m.d 3 4) (by simp) with h445 | h445
                      · linarith only [h441, h445, hc34, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                      · rcases p347_3 (m.d 3 5) (by simp) with h447 | h447
                        · linarith only [h447, hlam, p347_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h449 | h449
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h450 | h450
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h451 | h451
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h452 | h452
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h453 | h453
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h454 | h454
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h455 | h455
                                      · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
                                        · linarith only [h339, h456, hlam]
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h458 | h458
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                                            · linarith only [h341, h459, hlam]
                                            · linarith only [h445, h452, h459, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p347_1, u1ehi2]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
                                            · linarith only [h341, h462, hlam]
                                            · linarith only [h445, h449, h452, h462, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p347_1, u1ehi2]
                                      · linarith only [h443, h449, h452, h455, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p347_1, u1ehi1]
                                    · linarith only [h454, hlam, p347_0]
                                  · linarith only [h445, h453, hlam, p347_1]
                                · linarith only [h443, h452, hc03, hlam, hphi, p347_1, u0ehi1]
                              · linarith only [h451, hlam, p0_0]
                            · linarith only [h450, hc13, hlam, hphi, ht01, u0ehi0]
                          · linarith only [h339, h449, hlam, p0_1]
                · linarith only [h440, hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [h341, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p347_1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [h341, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p347_1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [h341, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p347_1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [h341, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p347_1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc23, hlam, hphi, ht01, ht12, p347_1, u0ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc23, hlam, hphi, ht12, p347_1, u1ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h481 | h481
                · rcases p347_3 (m.d 1 3) (by simp) with h482 | h482
                  · linarith only [h341, h482, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p347_1]
                  · linarith only [h482, hc23, hlam, hphi, ht12, p347_1, u1ehi2]
                · linarith only [h481, hc23, hlam, hphi, ht01, ht12, p347_1, u0ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h486 | h486
                · rcases p347_3 (m.d 1 3) (by simp) with h487 | h487
                  · linarith only [h341, h487, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p347_1]
                  · linarith only [h487, hc23, hlam, hphi, ht12, p347_1, u1ehi2]
                · linarith only [h486, hc23, hlam, hphi, ht01, ht12, p347_1, u0ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p347_1, u0ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc34, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h493 | h493
                · rcases p347_3 (m.d 1 3) (by simp) with h494 | h494
                  · linarith only [h341, h494, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p347_1]
                  · linarith only [h494, hc34, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                · linarith only [h493, hc34, hlam, hphi, ht01, ht12, ht23, p347_1, u0ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h499 | h499
                · rcases p347_3 (m.d 1 3) (by simp) with h500 | h500
                  · linarith only [h341, h500, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p347_1]
                  · linarith only [h500, hc34, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                · linarith only [h499, hc34, hlam, hphi, ht01, ht12, ht23, p347_1, u0ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p347_1, u0ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h506 | h506
                · rcases p347_3 (m.d 1 3) (by simp) with h507 | h507
                  · linarith only [h341, h507, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p347_1]
                  · linarith only [h507, hc35, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                · linarith only [h506, hc35, hlam, hphi, ht01, ht12, ht23, p347_1, u0ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                rcases p347_3 (m.d 0 3) (by simp) with h511 | h511
                · rcases p347_3 (m.d 1 3) (by simp) with h512 | h512
                  · linarith only [h341, h512, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p347_1]
                  · linarith only [h512, hc35, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                · linarith only [h511, hc35, hlam, hphi, ht01, ht12, ht23, p347_1, u0ehi2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
    · linarith only [h338, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h518 | h518
    · rcases p0_3 (m.d 1 2) (by simp) with h519 | h519
      · linarith only [h519, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h521 | h521
        · linarith only [h521, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h523 | h523
          · linarith only [h523, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h525 | h525
            · linarith only [h525, hlam, p0_0]
            · rcases h3bigk with h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hlam, p527_0]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h529 | h529
                · rcases p527_3 (m.d 1 3) (by simp) with h530 | h530
                  · linarith only [h530, hlam, p527_0]
                  · rcases p527_3 (m.d 2 3) (by simp) with h532 | h532
                    · linarith only [h532, hc23, hlam, hphi, ht12, p527_1, u1ehi2]
                    · rcases p527_3 (m.d 3 4) (by simp) with h534 | h534
                      · linarith only [h534, hc34, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                      · rcases p527_3 (m.d 3 5) (by simp) with h536 | h536
                        · linarith only [h536, hc35, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h538 | h538
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h539 | h539
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h540 | h540
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h541 | h541
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h542 | h542
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h543 | h543
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
                                      · rcases m.htr 1 2 4 (by decide) (by decide) with h545 | h545
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h546 | h546
                                          · linarith only [h519, h546, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h549 | h549
                                              · linarith only [h521, h549, hlam]
                                              · linarith only [h536, h549, hlam]
                                            · linarith only [h534, h548, hlam]
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
                                          · linarith only [h519, h553, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h555 | h555
                                            · linarith only [h544, h545, h555, hlam]
                                            · linarith only [h534, h555, hlam]
                                      · linarith only [h532, h544, hlam]
                                    · linarith only [h536, h543, hlam, p527_1]
                                  · linarith only [h542, hc34, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                                · linarith only [h541, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h523, h540, hlam, p0_1]
                            · linarith only [h539, hlam, p527_0]
                          · linarith only [h538, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h529, hlam, p527_0]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h566 | h566
                · rcases p527_3 (m.d 1 3) (by simp) with h567 | h567
                  · linarith only [h521, h567, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p527_3 (m.d 2 3) (by simp) with h569 | h569
                    · linarith only [h569, hlam, p527_0]
                    · rcases p527_3 (m.d 3 4) (by simp) with h571 | h571
                      · linarith only [h567, h571, hc34, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                      · rcases p527_3 (m.d 3 5) (by simp) with h573 | h573
                        · linarith only [h567, h573, hc35, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h575 | h575
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h576 | h576
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h577 | h577
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h578 | h578
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h579 | h579
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h580 | h580
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h581 | h581
                                      · linarith only [h567, h581, hlam]
                                      · linarith only [h575, h578, h581, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p527_1, u1ehi1]
                                    · linarith only [h573, h580, hlam, p527_1]
                                  · linarith only [h571, h579, hlam, p527_1]
                                · linarith only [h578, hlam, p527_0]
                              · linarith only [h523, h577, hlam, p0_1]
                            · linarith only [h576, hc13, hlam, hphi, ht01, u0ehi0]
                          · linarith only [h523, h575, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h566, hlam, p527_0]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h591 | h591
                · rcases p527_3 (m.d 1 3) (by simp) with h592 | h592
                  · linarith only [h521, h592, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p527_3 (m.d 2 3) (by simp) with h594 | h594
                    · linarith only [h592, h594, hc23, hlam, hphi, ht12, p527_1, u1ehi2]
                    · rcases p527_3 (m.d 3 4) (by simp) with h596 | h596
                      · linarith only [h596, hlam, p527_0]
                      · rcases p527_3 (m.d 3 5) (by simp) with h598 | h598
                        · linarith only [h592, h598, hc35, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h600 | h600
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h601 | h601
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h602 | h602
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h603 | h603
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h604 | h604
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h605 | h605
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                                      · rcases m.htr 1 2 4 (by decide) (by decide) with h607 | h607
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
                                          · linarith only [h519, h608, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
                                            · linarith only [h592, h610, hlam]
                                            · linarith only [h603, h610, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p527_1, u1ehi2]
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h613 | h613
                                          · linarith only [h519, h613, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h615 | h615
                                            · linarith only [h592, h615, hlam]
                                            · linarith only [h600, h603, h615, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p527_1, u1ehi2]
                                      · linarith only [h594, h600, h603, h606, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p527_1, u1ehi1]
                                    · linarith only [h598, h605, hlam, p527_1]
                                  · linarith only [h604, hlam, p527_0]
                                · linarith only [h594, h603, hc03, hlam, hphi, p527_1, u0ehi1]
                              · linarith only [h523, h602, hlam, p0_1]
                            · linarith only [h601, hc13, hlam, hphi, ht01, u0ehi0]
                          · linarith only [h523, h600, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h591, hlam, p527_0]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h626 | h626
                · rcases p527_3 (m.d 1 3) (by simp) with h627 | h627
                  · linarith only [h521, h627, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p527_3 (m.d 2 3) (by simp) with h629 | h629
                    · linarith only [h627, h629, hc23, hlam, hphi, ht12, p527_1, u1ehi2]
                    · rcases p527_3 (m.d 3 4) (by simp) with h631 | h631
                      · linarith only [h627, h631, hc34, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                      · rcases p527_3 (m.d 3 5) (by simp) with h633 | h633
                        · linarith only [h633, hlam, p527_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h635 | h635
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h636 | h636
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h637 | h637
                              · rcases m.htr 0 2 3 (by decide) (by decide) with h638 | h638
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h639 | h639
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h640 | h640
                                    · rcases m.htr 1 2 3 (by decide) (by decide) with h641 | h641
                                      · rcases m.htr 1 2 4 (by decide) (by decide) with h642 | h642
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h643 | h643
                                          · linarith only [h519, h643, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h645 | h645
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h646 | h646
                                              · linarith only [h521, h646, hlam]
                                              · linarith only [h638, h645, h646, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p527_1, u1ehi3]
                                            · linarith only [h631, h635, h638, h645, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p527_1, u1ehi2]
                                        · rcases m.htr 1 2 5 (by decide) (by decide) with h650 | h650
                                          · linarith only [h519, h650, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h652 | h652
                                            · linarith only [h641, h642, h652, hlam]
                                            · linarith only [h631, h635, h638, h652, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p527_1, u1ehi2]
                                      · linarith only [h629, h635, h638, h641, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p527_1, u1ehi1]
                                    · linarith only [h640, hlam, p527_0]
                                  · linarith only [h631, h639, hlam, p527_1]
                                · linarith only [h629, h638, hc03, hlam, hphi, p527_1, u0ehi1]
                              · linarith only [h637, hc14, hlam, hphi, ht01, u0ehi0]
                            · linarith only [h627, h636, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, p527_1, u1ehi4]
                          · linarith only [h635, hc12, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h626, hlam, p527_0]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [h521, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p527_1]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hlam, p527_0]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [h521, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p527_1]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [h521, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p527_1]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [h521, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p527_1]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hc23, hlam, hphi, ht01, ht12, p527_1, u0ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hc23, hlam, hphi, ht12, p527_1, u1ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hlam, p527_0]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h671 | h671
                · rcases p527_3 (m.d 1 3) (by simp) with h672 | h672
                  · linarith only [h521, h672, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p527_1]
                  · linarith only [h672, hc23, hlam, hphi, ht12, p527_1, u1ehi2]
                · linarith only [h671, hc23, hlam, hphi, ht01, ht12, p527_1, u0ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h676 | h676
                · rcases p527_3 (m.d 1 3) (by simp) with h677 | h677
                  · linarith only [h521, h677, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p527_1]
                  · linarith only [h677, hc23, hlam, hphi, ht12, p527_1, u1ehi2]
                · linarith only [h676, hc23, hlam, hphi, ht01, ht12, p527_1, u0ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p527_1, u0ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hc34, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h683 | h683
                · rcases p527_3 (m.d 1 3) (by simp) with h684 | h684
                  · linarith only [h521, h684, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p527_1]
                  · linarith only [h684, hc34, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                · linarith only [h683, hc34, hlam, hphi, ht01, ht12, ht23, p527_1, u0ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hlam, p527_0]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h689 | h689
                · rcases p527_3 (m.d 1 3) (by simp) with h690 | h690
                  · linarith only [h521, h690, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p527_1]
                  · linarith only [h690, hc34, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                · linarith only [h689, hc34, hlam, hphi, ht01, ht12, ht23, p527_1, u0ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p527_1, u0ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h696 | h696
                · rcases p527_3 (m.d 1 3) (by simp) with h697 | h697
                  · linarith only [h521, h697, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p527_1]
                  · linarith only [h697, hc35, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                · linarith only [h696, hc35, hlam, hphi, ht01, ht12, ht23, p527_1, u0ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                rcases p527_3 (m.d 0 3) (by simp) with h701 | h701
                · rcases p527_3 (m.d 1 3) (by simp) with h702 | h702
                  · linarith only [h521, h702, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p527_1]
                  · linarith only [h702, hc35, hlam, hphi, ht12, ht23, p527_1, u1ehi2]
                · linarith only [h701, hc35, hlam, hphi, ht01, ht12, ht23, p527_1, u0ehi2]
              · have p527_0 := h527c.1
                have p527_1 := h527c.2.1
                have p527_2 := h527c.2.2.1
                have p527_3 := h527c.2.2.2
                linarith only [hlam, p527_0]
    · linarith only [h518, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_IR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc13, hlam, hphi, p0_1, u1ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · linarith only [h7, hc14, hlam, hphi, p0_1, u1ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h9 | h9
            · linarith only [h9, hc15, hlam, hphi, p0_1, u1ehi1]
            · rcases h3bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h13 | h13
                · rcases p11_3 (m.d 1 3) (by simp) with h14 | h14
                  · linarith only [h14, hlam, p11_0]
                  · rcases p11_3 (m.d 2 3) (by simp) with h16 | h16
                    · linarith only [h16, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                    · rcases p11_3 (m.d 3 4) (by simp) with h18 | h18
                      · linarith only [h18, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                      · rcases p11_3 (m.d 3 5) (by simp) with h20 | h20
                        · linarith only [h20, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h22 | h22
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h23 | h23
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h25 | h25
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h27 | h27
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h28 | h28
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h29 | h29
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                                                        · linarith only [h31, h37, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                        · linarith only [h22, h26, h34, h37, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                                                        · linarith only [h31, h40, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                        · linarith only [h22, h26, h34, h40, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                    · linarith only [h20, h35, hlam]
                                                  · linarith only [h18, h34, hlam]
                                                · linarith only [h33, h9, hlam]
                                              · linarith only [h32, h7, hlam]
                                            · linarith only [h16, h31, hlam]
                                          · linarith only [h30, hc13, hc35, hlam, hphi, p11_1]
                                        · linarith only [h29, hc13, hc34, hlam, hphi, p11_1]
                                      · linarith only [h26, h28, hc25, hlam, hphi, ht12, p11_1, u1ehi2]
                                    · linarith only [h26, h27, hc24, hlam, hphi, ht12, p11_1, u1ehi2]
                                  · linarith only [h16, h26, hc03, hlam, hphi, p11_1, u0ehi1]
                                · linarith only [h23, h25, hc15, hlam, hphi, p11_1, u1ehi2]
                              · linarith only [h23, h24, hc14, hlam, hphi, p11_1, u1ehi2]
                            · linarith only [h23, hlam, p11_0]
                          · linarith only [h22, hlam, p0_0]
                · linarith only [h13, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h58 | h58
                · rcases p11_3 (m.d 1 3) (by simp) with h59 | h59
                  · linarith only [h5, h59, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p11_3 (m.d 2 3) (by simp) with h61 | h61
                    · linarith only [h61, hlam, p11_0]
                    · rcases p11_3 (m.d 3 4) (by simp) with h63 | h63
                      · linarith only [h59, h63, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                      · rcases p11_3 (m.d 3 5) (by simp) with h65 | h65
                        · linarith only [h59, h65, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h67 | h67
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h68 | h68
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h69 | h69
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h70 | h70
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h71 | h71
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h72 | h72
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h73 | h73
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h75 | h75
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                                            · linarith only [h59, h76, hlam]
                                            · linarith only [h5, h76, hlam]
                                          · linarith only [h65, h75, hlam, p11_1]
                                        · linarith only [h63, h74, hlam, p11_1]
                                      · linarith only [h59, h71, h73, hc25, hlam, hphi, ht12, p11_1, u1ehi2]
                                    · linarith only [h59, h71, h72, hc24, hlam, hphi, ht12, p11_1, u1ehi2]
                                  · linarith only [h71, hlam, p11_0]
                                · linarith only [h70, h9, hlam, p0_1]
                              · linarith only [h69, h7, hlam, p0_1]
                            · linarith only [h59, h68, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                          · linarith only [h67, hlam, p0_0]
                · linarith only [h58, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h89 | h89
                · rcases p11_3 (m.d 1 3) (by simp) with h90 | h90
                  · linarith only [h5, h90, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p11_3 (m.d 2 3) (by simp) with h92 | h92
                    · linarith only [h90, h92, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                    · rcases p11_3 (m.d 3 4) (by simp) with h94 | h94
                      · linarith only [h94, hlam, p11_0]
                      · rcases p11_3 (m.d 3 5) (by simp) with h96 | h96
                        · linarith only [h90, h96, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h98 | h98
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h99 | h99
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h100 | h100
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h101 | h101
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h102 | h102
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h103 | h103
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h104 | h104
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h105 | h105
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h106 | h106
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                                                  · linarith only [h110, h90, hlam]
                                                  · linarith only [h102, h110, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                                · linarith only [h109, h9, hlam]
                                              · linarith only [h108, h7, hlam]
                                            · linarith only [h107, h5, hlam]
                                          · linarith only [h106, h96, hlam, p11_1]
                                        · linarith only [h105, hlam, p11_0]
                                      · linarith only [h102, h104, h90, hc25, hlam, hphi, ht12, p11_1, u1ehi2]
                                    · linarith only [h102, h103, h90, hc24, hlam, hphi, ht12, p11_1, u1ehi2]
                                  · linarith only [h102, h92, hc03, hlam, hphi, p11_1, u0ehi1]
                                · linarith only [h101, hc15, hlam, hphi, p0_1, u1ehi1]
                              · linarith only [h100, h90, h99, hc14, hlam, hphi, p11_1, u1ehi2]
                            · linarith only [h90, h99, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                          · linarith only [h98, hlam, p0_0]
                · linarith only [h89, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h126 | h126
                · rcases p11_3 (m.d 1 3) (by simp) with h127 | h127
                  · linarith only [h127, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · rcases p11_3 (m.d 2 3) (by simp) with h129 | h129
                    · linarith only [h127, h129, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                    · rcases p11_3 (m.d 3 4) (by simp) with h131 | h131
                      · linarith only [h127, h131, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                      · rcases p11_3 (m.d 3 5) (by simp) with h133 | h133
                        · linarith only [h133, hlam, p11_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h135 | h135
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h136 | h136
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h137 | h137
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h138 | h138
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h139 | h139
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h140 | h140
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h141 | h141
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h142 | h142
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h143 | h143
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h146 | h146
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h147 | h147
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h148 | h148
                                                    · linarith only [h127, h148, hlam]
                                                    · linarith only [h135, h139, h147, h148, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi3]
                                                  · linarith only [h131, h135, h139, h147, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                                · linarith only [h146, h9, hlam]
                                              · linarith only [h145, h7, hlam]
                                            · linarith only [h144, h5, hlam]
                                          · linarith only [h143, hlam, p11_0]
                                        · linarith only [h131, h142, hlam, p11_1]
                                      · linarith only [h127, h139, h141, hc25, hlam, hphi, ht12, p11_1, u1ehi2]
                                    · linarith only [h127, h139, h140, hc24, hlam, hphi, ht12, p11_1, u1ehi2]
                                  · linarith only [h129, h136, h139, hc01, hlam, hphi, p11_1, u0ehi1]
                                · linarith only [h127, h136, h138, hc15, hlam, hphi, p11_1, u1ehi2]
                              · linarith only [h127, h136, h137, hc14, hlam, hphi, p11_1, u1ehi2]
                            · linarith only [h127, h136, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                          · linarith only [h135, hlam, p0_0]
                · linarith only [h126, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc23, hlam, hphi, ht01, ht12, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc23, hlam, hphi, ht12, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h173 | h173
                · rcases p11_3 (m.d 1 3) (by simp) with h174 | h174
                  · linarith only [h174, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h174, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                · linarith only [h173, hc23, hlam, hphi, ht01, ht12, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h178 | h178
                · rcases p11_3 (m.d 1 3) (by simp) with h179 | h179
                  · linarith only [h179, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h179, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                · linarith only [h178, hc23, hlam, hphi, ht01, ht12, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h185 | h185
                · rcases p11_3 (m.d 1 3) (by simp) with h186 | h186
                  · linarith only [h186, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h186, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · linarith only [h185, hc34, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h191 | h191
                · rcases p11_3 (m.d 1 3) (by simp) with h192 | h192
                  · linarith only [h192, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h192, hc34, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · linarith only [h191, hc34, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h198 | h198
                · rcases p11_3 (m.d 1 3) (by simp) with h199 | h199
                  · linarith only [h199, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h199, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · linarith only [h198, hc35, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                rcases p11_3 (m.d 0 3) (by simp) with h203 | h203
                · rcases p11_3 (m.d 1 3) (by simp) with h204 | h204
                  · linarith only [h204, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h204, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi2]
                · linarith only [h203, hc35, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi2]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h210 | h210
    · rcases p0_3 (m.d 1 2) (by simp) with h211 | h211
      · linarith only [h211, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h213 | h213
        · linarith only [h213, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h215 | h215
          · linarith only [h215, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h217 | h217
            · linarith only [h217, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases h3bigk with h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hlam, p219_0]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h221 | h221
                · rcases p219_3 (m.d 1 3) (by simp) with h222 | h222
                  · linarith only [h222, hlam, p219_0]
                  · rcases p219_3 (m.d 2 3) (by simp) with h224 | h224
                    · linarith only [h224, hc23, hlam, hphi, ht12, p219_1, u1ehi2]
                    · rcases p219_3 (m.d 3 4) (by simp) with h226 | h226
                      · linarith only [h226, hc34, hlam, hphi, ht12, ht23, p219_1, u1ehi2]
                      · rcases p219_3 (m.d 3 5) (by simp) with h228 | h228
                        · linarith only [h228, hc35, hlam, hphi, ht12, ht23, p219_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h230 | h230
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h231 | h231
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h232 | h232
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h233 | h233
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h234 | h234
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h235 | h235
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h236 | h236
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h237 | h237
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h238 | h238
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
                                            · linarith only [h211, h239, hlam]
                                            · linarith only [h224, h239, hlam]
                                          · linarith only [h228, h238, hlam, p219_1]
                                        · linarith only [h226, h237, hlam, p219_1]
                                      · linarith only [h234, h236, hc25, hlam, hphi, ht12, p219_1, u1ehi2]
                                    · linarith only [h234, h235, hc24, hlam, hphi, ht12, p219_1, u1ehi2]
                                  · linarith only [h224, h234, hc03, hlam, hphi, p219_1, u0ehi1]
                                · linarith only [h217, h231, h233, hlam, p219_1]
                              · linarith only [h215, h231, h232, hlam, p219_1]
                            · linarith only [h231, hlam, p0_0]
                          · linarith only [h211, h230, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p219_1, u1ehi0]
                · linarith only [h221, hlam, p219_0]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h252 | h252
                · rcases p219_3 (m.d 1 3) (by simp) with h253 | h253
                  · linarith only [h253, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p219_1]
                  · rcases p219_3 (m.d 2 3) (by simp) with h255 | h255
                    · linarith only [h255, hlam, p219_0]
                    · rcases p219_3 (m.d 3 4) (by simp) with h257 | h257
                      · linarith only [h211, h253, h257, hc34, hlam, hphi, ht12, ht23, p219_1, u1ehi1]
                      · rcases p219_3 (m.d 3 5) (by simp) with h259 | h259
                        · linarith only [h211, h253, h259, hc35, hlam, hphi, ht12, ht23, p219_1, u1ehi1]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h261 | h261
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h262 | h262
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h263 | h263
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h264 | h264
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h265 | h265
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h266 | h266
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h267 | h267
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h268 | h268
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h269 | h269
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
                                            · linarith only [h211, h270, hlam]
                                            · linarith only [h261, h265, h270, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p219_1, u1ehi1]
                                          · linarith only [h259, h269, hlam, p219_1]
                                        · linarith only [h257, h268, hlam, p219_1]
                                      · linarith only [h253, h265, h267, hc25, hlam, hphi, ht12, p219_1, u1ehi2]
                                    · linarith only [h253, h265, h266, hc24, hlam, hphi, ht12, p219_1, u1ehi2]
                                  · linarith only [h265, hlam, p219_0]
                                · linarith only [h217, h253, h264, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p219_1, u1ehi0]
                              · linarith only [h215, h253, h262, h263, hlam, p219_1]
                            · linarith only [h262, hlam, p0_0]
                          · linarith only [h261, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h252, hlam, p219_0]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h283 | h283
                · rcases p219_3 (m.d 1 3) (by simp) with h284 | h284
                  · linarith only [h284, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p219_3 (m.d 2 3) (by simp) with h286 | h286
                    · linarith only [h211, h284, h286, hc23, hlam, hphi, ht12, p219_1, u1ehi1]
                    · rcases p219_3 (m.d 3 4) (by simp) with h288 | h288
                      · linarith only [h288, hlam, p219_0]
                      · rcases p219_3 (m.d 3 5) (by simp) with h290 | h290
                        · linarith only [h211, h284, h290, hc35, hlam, hphi, ht12, ht23, p219_1, u1ehi1]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h292 | h292
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h293 | h293
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h294 | h294
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h295 | h295
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h296 | h296
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h297 | h297
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h298 | h298
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h299 | h299
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h300 | h300
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
                                            · linarith only [h211, h301, hlam]
                                            · linarith only [h286, h296, h301, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p219_1, u1ehi1]
                                          · linarith only [h290, h300, hlam, p219_1]
                                        · linarith only [h299, hlam, p219_0]
                                      · linarith only [h284, h296, h298, hc25, hlam, hphi, ht12, p219_1, u1ehi2]
                                    · linarith only [h284, h296, h297, hc24, hlam, hphi, ht12, p219_1, u1ehi2]
                                  · linarith only [h286, h296, hc03, hlam, hphi, p219_1, u0ehi1]
                                · linarith only [h217, h284, h293, h295, hlam, p219_1]
                              · linarith only [h284, h293, h294, hc14, hlam, hphi, p219_1, u1ehi2]
                            · linarith only [h293, hlam, p0_0]
                          · linarith only [h292, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h283, hlam, p219_0]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h314 | h314
                · rcases p219_3 (m.d 1 3) (by simp) with h315 | h315
                  · linarith only [h315, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p219_3 (m.d 2 3) (by simp) with h317 | h317
                    · linarith only [h211, h315, h317, hc23, hlam, hphi, ht12, p219_1, u1ehi1]
                    · rcases p219_3 (m.d 3 4) (by simp) with h319 | h319
                      · linarith only [h211, h315, h319, hc34, hlam, hphi, ht12, ht23, p219_1, u1ehi1]
                      · rcases p219_3 (m.d 3 5) (by simp) with h321 | h321
                        · linarith only [h321, hlam, p219_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h323 | h323
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h324 | h324
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h325 | h325
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h326 | h326
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h327 | h327
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h328 | h328
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h329 | h329
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h330 | h330
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h331 | h331
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                                            · linarith only [h211, h332, hlam]
                                            · linarith only [h317, h323, h327, h332, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p219_1, u1ehi1]
                                          · linarith only [h331, hlam, p219_0]
                                        · linarith only [h319, h330, hlam, p219_1]
                                      · linarith only [h315, h327, h329, hc25, hlam, hphi, ht12, p219_1, u1ehi2]
                                    · linarith only [h315, h327, h328, hc24, hlam, hphi, ht12, p219_1, u1ehi2]
                                  · linarith only [h317, h327, hc03, hlam, hphi, p219_1, u0ehi1]
                                · linarith only [h217, h315, h324, h326, hlam, p219_1]
                              · linarith only [h315, h324, h325, hc14, hlam, hphi, p219_1, u1ehi2]
                            · linarith only [h324, hlam, p0_0]
                          · linarith only [h323, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h314, hlam, p219_0]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p219_1]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hlam, p219_0]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p219_1]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p219_1]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p219_1]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hc23, hlam, hphi, ht01, ht12, p219_1, u0ehi2]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [h211, hc23, hlam, hphi, ht12, p219_1, u1ehi1]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hlam, p219_0]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h353 | h353
                · rcases p219_3 (m.d 1 3) (by simp) with h354 | h354
                  · linarith only [h354, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p219_1]
                  · linarith only [h354, hc23, hlam, hphi, ht12, p219_1, u1ehi2]
                · linarith only [h353, hc23, hlam, hphi, ht01, ht12, p219_1, u0ehi2]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h358 | h358
                · rcases p219_3 (m.d 1 3) (by simp) with h359 | h359
                  · linarith only [h359, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p219_1]
                  · linarith only [h359, hc23, hlam, hphi, ht12, p219_1, u1ehi2]
                · linarith only [h358, hc23, hlam, hphi, ht01, ht12, p219_1, u0ehi2]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p219_1, u0ehi2]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [h211, hc34, hlam, hphi, ht12, ht23, p219_1, u1ehi1]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h365 | h365
                · rcases p219_3 (m.d 1 3) (by simp) with h366 | h366
                  · linarith only [h366, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p219_1]
                  · linarith only [h366, hc34, hlam, hphi, ht12, ht23, p219_1, u1ehi2]
                · linarith only [h365, hc34, hlam, hphi, ht01, ht12, ht23, p219_1, u0ehi2]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hlam, p219_0]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h371 | h371
                · rcases p219_3 (m.d 1 3) (by simp) with h372 | h372
                  · linarith only [h372, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p219_1]
                  · linarith only [h372, hc34, hlam, hphi, ht12, ht23, p219_1, u1ehi2]
                · linarith only [h371, hc34, hlam, hphi, ht01, ht12, ht23, p219_1, u0ehi2]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p219_1, u0ehi2]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [h215, hc35, hlam, hphi, ht12, ht23, p219_1, u1ehi3]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h378 | h378
                · rcases p219_3 (m.d 1 3) (by simp) with h379 | h379
                  · linarith only [h379, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p219_1]
                  · linarith only [h379, hc35, hlam, hphi, ht12, ht23, p219_1, u1ehi2]
                · linarith only [h378, hc35, hlam, hphi, ht01, ht12, ht23, p219_1, u0ehi2]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                rcases p219_3 (m.d 0 3) (by simp) with h383 | h383
                · rcases p219_3 (m.d 1 3) (by simp) with h384 | h384
                  · linarith only [h384, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p219_1]
                  · linarith only [h384, hc35, hlam, hphi, ht12, ht23, p219_1, u1ehi2]
                · linarith only [h383, hc35, hlam, hphi, ht01, ht12, ht23, p219_1, u0ehi2]
              · have p219_0 := h219c.1
                have p219_1 := h219c.2.1
                have p219_2 := h219c.2.2.1
                have p219_3 := h219c.2.2.2
                linarith only [hlam, p219_0]
    · linarith only [h210, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h390 | h390
    · rcases p0_3 (m.d 1 2) (by simp) with h391 | h391
      · linarith only [h391, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h393 | h393
        · linarith only [h393, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h395 | h395
          · linarith only [h395, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h397 | h397
            · linarith only [h397, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases h3bigk with h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h401 | h401
                · rcases p399_3 (m.d 1 3) (by simp) with h402 | h402
                  · linarith only [h402, hlam, p399_0]
                  · rcases p399_3 (m.d 2 3) (by simp) with h404 | h404
                    · linarith only [h404, hc23, hlam, hphi, ht12, p399_1, u1ehi2]
                    · rcases p399_3 (m.d 3 4) (by simp) with h406 | h406
                      · linarith only [h406, hc34, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                      · rcases p399_3 (m.d 3 5) (by simp) with h408 | h408
                        · linarith only [h408, hc35, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h410 | h410
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h411 | h411
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h412 | h412
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h413 | h413
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h414 | h414
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h415 | h415
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h416 | h416
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h417 | h417
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h418 | h418
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h420 | h420
                                              · linarith only [h391, h420, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h422 | h422
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
                                                  · linarith only [h393, h423, hlam]
                                                  · linarith only [h406, h423, hlam]
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h426 | h426
                                                  · linarith only [h393, h426, hlam]
                                                  · linarith only [h406, h426, hlam]
                                            · linarith only [h404, h419, hlam]
                                          · linarith only [h408, h418, hlam, p399_1]
                                        · linarith only [h406, h417, hlam, p399_1]
                                      · linarith only [h414, h416, hc25, hlam, hphi, ht12, p399_1, u1ehi2]
                                    · linarith only [h414, h415, hc24, hlam, hphi, ht12, p399_1, u1ehi2]
                                  · linarith only [h404, h414, hc03, hlam, hphi, p399_1, u0ehi1]
                                · linarith only [h397, h413, hlam, p0_1]
                              · linarith only [h412, hlam, p0_0]
                            · linarith only [h411, hlam, p399_0]
                          · linarith only [h410, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h401, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h440 | h440
                · rcases p399_3 (m.d 1 3) (by simp) with h441 | h441
                  · linarith only [h393, h441, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p399_3 (m.d 2 3) (by simp) with h443 | h443
                    · linarith only [h443, hlam, p399_0]
                    · rcases p399_3 (m.d 3 4) (by simp) with h445 | h445
                      · linarith only [h441, h445, hc34, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                      · rcases p399_3 (m.d 3 5) (by simp) with h447 | h447
                        · linarith only [h441, h447, hc35, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h449 | h449
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h450 | h450
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h451 | h451
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h452 | h452
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h453 | h453
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h454 | h454
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h455 | h455
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h456 | h456
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h457 | h457
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
                                            · linarith only [h441, h458, hlam]
                                            · linarith only [h449, h453, h458, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi1]
                                          · linarith only [h447, h457, hlam, p399_1]
                                        · linarith only [h445, h456, hlam, p399_1]
                                      · linarith only [h441, h453, h455, hc25, hlam, hphi, ht12, p399_1, u1ehi2]
                                    · linarith only [h441, h453, h454, hc24, hlam, hphi, ht12, p399_1, u1ehi2]
                                  · linarith only [h453, hlam, p399_0]
                                · linarith only [h397, h452, hlam, p0_1]
                              · linarith only [h451, hlam, p0_0]
                            · linarith only [h441, h450, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi0]
                          · linarith only [h449, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h440, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h471 | h471
                · rcases p399_3 (m.d 1 3) (by simp) with h472 | h472
                  · linarith only [h393, h472, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p399_3 (m.d 2 3) (by simp) with h474 | h474
                    · linarith only [h472, h474, hc23, hlam, hphi, ht12, p399_1, u1ehi2]
                    · rcases p399_3 (m.d 3 4) (by simp) with h476 | h476
                      · linarith only [h476, hlam, p399_0]
                      · rcases p399_3 (m.d 3 5) (by simp) with h478 | h478
                        · linarith only [h472, h478, hc35, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h480 | h480
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h481 | h481
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h482 | h482
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h483 | h483
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h484 | h484
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h485 | h485
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h486 | h486
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h487 | h487
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h488 | h488
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                                              · linarith only [h391, h490, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                                                  · linarith only [h393, h493, hlam]
                                                  · linarith only [h480, h484, h493, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi2]
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h496 | h496
                                                  · linarith only [h393, h496, hlam]
                                                  · linarith only [h480, h484, h496, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi2]
                                            · linarith only [h474, h480, h484, h489, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi1]
                                          · linarith only [h478, h488, hlam, p399_1]
                                        · linarith only [h487, hlam, p399_0]
                                      · linarith only [h472, h484, h486, hc25, hlam, hphi, ht12, p399_1, u1ehi2]
                                    · linarith only [h472, h484, h485, hc24, hlam, hphi, ht12, p399_1, u1ehi2]
                                  · linarith only [h474, h484, hc03, hlam, hphi, p399_1, u0ehi1]
                                · linarith only [h397, h483, hlam, p0_1]
                              · linarith only [h482, hlam, p0_0]
                            · linarith only [h472, h481, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi0]
                          · linarith only [h480, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h471, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h510 | h510
                · rcases p399_3 (m.d 1 3) (by simp) with h511 | h511
                  · linarith only [h393, h511, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p399_3 (m.d 2 3) (by simp) with h513 | h513
                    · linarith only [h511, h513, hc23, hlam, hphi, ht12, p399_1, u1ehi2]
                    · rcases p399_3 (m.d 3 4) (by simp) with h515 | h515
                      · linarith only [h511, h515, hc34, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                      · rcases p399_3 (m.d 3 5) (by simp) with h517 | h517
                        · linarith only [h517, hlam, p399_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h519 | h519
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h520 | h520
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h521 | h521
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h522 | h522
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h523 | h523
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h524 | h524
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h525 | h525
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h526 | h526
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h527 | h527
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h528 | h528
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h529 | h529
                                              · linarith only [h391, h529, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h531 | h531
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h532 | h532
                                                  · linarith only [h393, h532, hlam]
                                                  · linarith only [h515, h519, h523, h532, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi2]
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
                                                  · linarith only [h393, h535, hlam]
                                                  · linarith only [h515, h519, h523, h535, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi2]
                                            · linarith only [h513, h519, h523, h528, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi1]
                                          · linarith only [h527, hlam, p399_0]
                                        · linarith only [h515, h526, hlam, p399_1]
                                      · linarith only [h511, h523, h525, hc25, hlam, hphi, ht12, p399_1, u1ehi2]
                                    · linarith only [h511, h523, h524, hc24, hlam, hphi, ht12, p399_1, u1ehi2]
                                  · linarith only [h513, h523, hc03, hlam, hphi, p399_1, u0ehi1]
                                · linarith only [h397, h522, hlam, p0_1]
                              · linarith only [h521, hlam, p0_0]
                            · linarith only [h511, h520, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p399_1, u1ehi0]
                          · linarith only [h519, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h510, hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h393, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p399_1]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h393, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p399_1]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h393, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p399_1]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [h393, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p399_1]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hc23, hlam, hphi, ht01, ht12, p399_1, u0ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hc23, hlam, hphi, ht12, p399_1, u1ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h557 | h557
                · rcases p399_3 (m.d 1 3) (by simp) with h558 | h558
                  · linarith only [h393, h558, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p399_1]
                  · linarith only [h558, hc23, hlam, hphi, ht12, p399_1, u1ehi2]
                · linarith only [h557, hc23, hlam, hphi, ht01, ht12, p399_1, u0ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h562 | h562
                · rcases p399_3 (m.d 1 3) (by simp) with h563 | h563
                  · linarith only [h393, h563, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p399_1]
                  · linarith only [h563, hc23, hlam, hphi, ht12, p399_1, u1ehi2]
                · linarith only [h562, hc23, hlam, hphi, ht01, ht12, p399_1, u0ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p399_1, u0ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hc34, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h569 | h569
                · rcases p399_3 (m.d 1 3) (by simp) with h570 | h570
                  · linarith only [h393, h570, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p399_1]
                  · linarith only [h570, hc34, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                · linarith only [h569, hc34, hlam, hphi, ht01, ht12, ht23, p399_1, u0ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h575 | h575
                · rcases p399_3 (m.d 1 3) (by simp) with h576 | h576
                  · linarith only [h393, h576, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p399_1]
                  · linarith only [h576, hc34, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                · linarith only [h575, hc34, hlam, hphi, ht01, ht12, ht23, p399_1, u0ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p399_1, u0ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h582 | h582
                · rcases p399_3 (m.d 1 3) (by simp) with h583 | h583
                  · linarith only [h393, h583, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p399_1]
                  · linarith only [h583, hc35, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                · linarith only [h582, hc35, hlam, hphi, ht01, ht12, ht23, p399_1, u0ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                rcases p399_3 (m.d 0 3) (by simp) with h587 | h587
                · rcases p399_3 (m.d 1 3) (by simp) with h588 | h588
                  · linarith only [h393, h588, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p399_1]
                  · linarith only [h588, hc35, hlam, hphi, ht12, ht23, p399_1, u1ehi2]
                · linarith only [h587, hc35, hlam, hphi, ht01, ht12, ht23, p399_1, u0ehi2]
              · have p399_0 := h399c.1
                have p399_1 := h399c.2.1
                have p399_2 := h399c.2.2.1
                have p399_3 := h399c.2.2.2
                linarith only [hlam, p399_0]
    · linarith only [h390, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h594 | h594
    · rcases p0_3 (m.d 1 2) (by simp) with h595 | h595
      · linarith only [h595, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h597 | h597
        · linarith only [h597, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h599 | h599
          · linarith only [h599, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h601 | h601
            · linarith only [h601, hlam, p0_0]
            · rcases h3bigk with h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h605 | h605
                · rcases p603_3 (m.d 1 3) (by simp) with h606 | h606
                  · linarith only [h606, hlam, p603_0]
                  · rcases p603_3 (m.d 2 3) (by simp) with h608 | h608
                    · linarith only [h608, hc23, hlam, hphi, ht12, p603_1, u1ehi2]
                    · rcases p603_3 (m.d 3 4) (by simp) with h610 | h610
                      · linarith only [h610, hc34, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                      · rcases p603_3 (m.d 3 5) (by simp) with h612 | h612
                        · linarith only [h612, hc35, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h614 | h614
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h615 | h615
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h616 | h616
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h617 | h617
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h618 | h618
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h619 | h619
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h620 | h620
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h621 | h621
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h622 | h622
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h623 | h623
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h624 | h624
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
                                                · linarith only [h595, h625, hlam]
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h627 | h627
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h628 | h628
                                                    · linarith only [h597, h628, hlam]
                                                    · linarith only [h612, h628, hlam]
                                                  · linarith only [h610, h627, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h632 | h632
                                                · linarith only [h595, h632, hlam]
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h634 | h634
                                                  · linarith only [h623, h624, h634, hlam]
                                                  · linarith only [h610, h634, hlam]
                                            · linarith only [h608, h623, hlam]
                                          · linarith only [h612, h622, hlam, p603_1]
                                        · linarith only [h621, hc34, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                                      · linarith only [h618, h620, hc25, hlam, hphi, ht12, p603_1, u1ehi2]
                                    · linarith only [h618, h619, hc24, hlam, hphi, ht12, p603_1, u1ehi2]
                                  · linarith only [h608, h618, hc03, hlam, hphi, p603_1, u0ehi1]
                                · linarith only [h617, hlam, p0_0]
                              · linarith only [h599, h616, hlam, p0_1]
                            · linarith only [h615, hlam, p603_0]
                          · linarith only [h597, h614, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h605, hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h648 | h648
                · rcases p603_3 (m.d 1 3) (by simp) with h649 | h649
                  · linarith only [h597, h649, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p603_3 (m.d 2 3) (by simp) with h651 | h651
                    · linarith only [h651, hlam, p603_0]
                    · rcases p603_3 (m.d 3 4) (by simp) with h653 | h653
                      · linarith only [h649, h653, hc34, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                      · rcases p603_3 (m.d 3 5) (by simp) with h655 | h655
                        · linarith only [h649, h655, hc35, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h657 | h657
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h658 | h658
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h659 | h659
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h660 | h660
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h661 | h661
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h662 | h662
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h663 | h663
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h664 | h664
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h665 | h665
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
                                            · linarith only [h649, h666, hlam]
                                            · linarith only [h661, h666, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi1]
                                          · linarith only [h655, h665, hlam, p603_1]
                                        · linarith only [h653, h664, hlam, p603_1]
                                      · linarith only [h649, h661, h663, hc25, hlam, hphi, ht12, p603_1, u1ehi2]
                                    · linarith only [h649, h661, h662, hc24, hlam, hphi, ht12, p603_1, u1ehi2]
                                  · linarith only [h661, hlam, p603_0]
                                · linarith only [h660, hlam, p0_0]
                              · linarith only [h599, h659, hlam, p0_1]
                            · linarith only [h649, h658, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi0]
                          · linarith only [h599, h657, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h648, hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h679 | h679
                · rcases p603_3 (m.d 1 3) (by simp) with h680 | h680
                  · linarith only [h597, h680, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p603_3 (m.d 2 3) (by simp) with h682 | h682
                    · linarith only [h680, h682, hc23, hlam, hphi, ht12, p603_1, u1ehi2]
                    · rcases p603_3 (m.d 3 4) (by simp) with h684 | h684
                      · linarith only [h684, hlam, p603_0]
                      · rcases p603_3 (m.d 3 5) (by simp) with h686 | h686
                        · linarith only [h680, h686, hc35, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h688 | h688
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h689 | h689
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h690 | h690
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h691 | h691
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h692 | h692
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h693 | h693
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h694 | h694
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h695 | h695
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h696 | h696
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h697 | h697
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h698 | h698
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h699 | h699
                                                · linarith only [h595, h699, hlam]
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h701 | h701
                                                  · linarith only [h680, h701, hlam]
                                                  · linarith only [h688, h692, h701, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi2]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h704 | h704
                                                · linarith only [h595, h704, hlam]
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h706 | h706
                                                  · linarith only [h680, h706, hlam]
                                                  · linarith only [h688, h692, h706, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi2]
                                            · linarith only [h682, h688, h692, h697, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi1]
                                          · linarith only [h686, h696, hlam, p603_1]
                                        · linarith only [h695, hlam, p603_0]
                                      · linarith only [h680, h692, h694, hc25, hlam, hphi, ht12, p603_1, u1ehi2]
                                    · linarith only [h680, h692, h693, hc24, hlam, hphi, ht12, p603_1, u1ehi2]
                                  · linarith only [h682, h692, hc03, hlam, hphi, p603_1, u0ehi1]
                                · linarith only [h691, hlam, p0_0]
                              · linarith only [h599, h690, hlam, p0_1]
                            · linarith only [h599, h689, hc13, hlam, hphi, p0_1, u1ehi3]
                          · linarith only [h599, h688, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h679, hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h720 | h720
                · rcases p603_3 (m.d 1 3) (by simp) with h721 | h721
                  · linarith only [h597, h721, hc01, hlam, hphi, p0_1, u0ehi2]
                  · rcases p603_3 (m.d 2 3) (by simp) with h723 | h723
                    · linarith only [h721, h723, hc23, hlam, hphi, ht12, p603_1, u1ehi2]
                    · rcases p603_3 (m.d 3 4) (by simp) with h725 | h725
                      · linarith only [h721, h725, hc34, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                      · rcases p603_3 (m.d 3 5) (by simp) with h727 | h727
                        · linarith only [h727, hlam, p603_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h729 | h729
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h730 | h730
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h731 | h731
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h732 | h732
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h733 | h733
                                  · rcases m.htr 0 2 4 (by decide) (by decide) with h734 | h734
                                    · rcases m.htr 0 2 5 (by decide) (by decide) with h735 | h735
                                      · rcases m.htr 0 3 4 (by decide) (by decide) with h736 | h736
                                        · rcases m.htr 0 3 5 (by decide) (by decide) with h737 | h737
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h738 | h738
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h739 | h739
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h740 | h740
                                                · linarith only [h595, h740, hlam]
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h742 | h742
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h743 | h743
                                                    · linarith only [h597, h743, hlam]
                                                    · linarith only [h729, h733, h742, h743, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi3]
                                                  · linarith only [h725, h729, h733, h742, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi2]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h747 | h747
                                                · linarith only [h595, h747, hlam]
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h749 | h749
                                                  · linarith only [h738, h739, h749, hlam]
                                                  · linarith only [h725, h729, h733, h749, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi2]
                                            · linarith only [h723, h729, h733, h738, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi1]
                                          · linarith only [h737, hlam, p603_0]
                                        · linarith only [h725, h736, hlam, p603_1]
                                      · linarith only [h721, h733, h735, hc25, hlam, hphi, ht12, p603_1, u1ehi2]
                                    · linarith only [h721, h733, h734, hc24, hlam, hphi, ht12, p603_1, u1ehi2]
                                  · linarith only [h723, h733, hc03, hlam, hphi, p603_1, u0ehi1]
                                · linarith only [h732, hlam, p0_0]
                              · linarith only [h599, h731, hlam, p0_1]
                            · linarith only [h721, h730, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p603_1, u1ehi0]
                          · linarith only [h599, h729, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h720, hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [h597, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p603_1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [h597, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p603_1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [h597, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p603_1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [h597, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p603_1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc23, hlam, hphi, ht01, ht12, p603_1, u0ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc23, hlam, hphi, ht12, p603_1, u1ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h771 | h771
                · rcases p603_3 (m.d 1 3) (by simp) with h772 | h772
                  · linarith only [h597, h772, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p603_1]
                  · linarith only [h772, hc23, hlam, hphi, ht12, p603_1, u1ehi2]
                · linarith only [h771, hc23, hlam, hphi, ht01, ht12, p603_1, u0ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h776 | h776
                · rcases p603_3 (m.d 1 3) (by simp) with h777 | h777
                  · linarith only [h597, h777, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p603_1]
                  · linarith only [h777, hc23, hlam, hphi, ht12, p603_1, u1ehi2]
                · linarith only [h776, hc23, hlam, hphi, ht01, ht12, p603_1, u0ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p603_1, u0ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc34, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h783 | h783
                · rcases p603_3 (m.d 1 3) (by simp) with h784 | h784
                  · linarith only [h597, h784, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p603_1]
                  · linarith only [h784, hc34, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                · linarith only [h783, hc34, hlam, hphi, ht01, ht12, ht23, p603_1, u0ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h789 | h789
                · rcases p603_3 (m.d 1 3) (by simp) with h790 | h790
                  · linarith only [h597, h790, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p603_1]
                  · linarith only [h790, hc34, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                · linarith only [h789, hc34, hlam, hphi, ht01, ht12, ht23, p603_1, u0ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p603_1, u0ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc35, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h796 | h796
                · rcases p603_3 (m.d 1 3) (by simp) with h797 | h797
                  · linarith only [h597, h797, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p603_1]
                  · linarith only [h797, hc35, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                · linarith only [h796, hc35, hlam, hphi, ht01, ht12, ht23, p603_1, u0ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                rcases p603_3 (m.d 0 3) (by simp) with h801 | h801
                · rcases p603_3 (m.d 1 3) (by simp) with h802 | h802
                  · linarith only [h597, h802, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p603_1]
                  · linarith only [h802, hc35, hlam, hphi, ht12, ht23, p603_1, u1ehi2]
                · linarith only [h801, hc35, hlam, hphi, ht01, ht12, ht23, p603_1, u0ehi2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
    · linarith only [h594, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LI_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1ehi := hb1.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
                                  · linarith only [h0, h10, h16, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h0, h10, h13, h16, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                · linarith only [h0, h15, h4, h7, h9, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                              · linarith only [h0, h13, h14, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h13, h4, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                          · linarith only [h0, h11, h12, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h10, h11, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h10, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                                · linarith only [h0, h25, h28, h30, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                                  · linarith only [h0, h25, h32, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h1, h28, h32, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h0, h28, h29, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h28, h4, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                          · linarith only [h0, h27, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                        · linarith only [h0, h25, h26, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h25, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
                    · linarith only [h40, h7, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h46 | h46
                              · linarith only [h2, h42, h46, h7, h8, hc12, hlam, hphi, u1ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
                                · linarith only [h2, h40, h48, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                                  · linarith only [h0, h42, h50, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h50, h7, h8, hc23, hc35, hlam, hphi]
                            · linarith only [h45, h7, h8, hc13, hc35, hlam, hphi]
                          · linarith only [h0, h43, h44, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h42, h43, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h4, h42, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                            · linarith only [h3, h57, h59, h62, h7, hc12, hlam, hphi, u1ehi4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                                  · linarith only [h0, h3, h57, h59, h66, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                                    · linarith only [h0, h60, h66, h68, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h57, h68, h7, hc23, hc34, hlam, hphi]
                                · linarith only [h58, h62, h64, h65, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                              · linarith only [h57, h64, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                          · linarith only [h0, h6, h60, h61, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h5, h59, h60, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h4, h59, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · linarith only [h57, h58, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                            · linarith only [h0, h7, h78, h81, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                              · linarith only [h1, h57, h83, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                                  · linarith only [h1, h7, h86, hc23, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                                    · linarith only [h1, h57, h79, h86, h88, hc12, hlam, hphi, u1ehi2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                                      · linarith only [h0, h79, h90, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h2, h85, h86, h90, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                · linarith only [h0, h5, h77, h85, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                          · linarith only [h0, h6, h80, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                        · linarith only [h0, h5, h78, h79, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h4, h78, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                            · linarith only [h1, h100, h7, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                              · linarith only [h1, h102, h57, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                                · linarith only [h1, h104, h7, h77, h98, hc12, hlam, hphi, u1ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                                  · linarith only [h0, h1, h106, h7, h97, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                                    · linarith only [h0, h1, h106, h108, h57, h98, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h110 | h110
                                      · linarith only [h0, h1, h110, h7, h77, h98, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                                        · linarith only [h1, h112, h7, h77, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                        · linarith only [h1, h112, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · linarith only [h0, h6, h99, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                        · linarith only [h0, h5, h97, h98, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h4, h97, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h118 | h118
                · rcases m.htr 0 3 5 (by decide) (by decide) with h119 | h119
                  · linarith only [h119, h4, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                    · linarith only [h121, h5, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                          · linarith only [h0, h125, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                              · linarith only [h118, h119, h123, h128, h2, hc12, hlam, hphi, u1ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                                · linarith only [h121, h130, h2, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                                  · linarith only [h123, h125, h132, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h118, h119, h132, hc23, hc35, hlam, hphi]
                            · linarith only [h118, h127, h4, h6, hc25, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h124, h5, h6, hc12, hc25, hlam, hphi]
                      · linarith only [h123, h4, h6, hc25, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h138 | h138
                  · linarith only [h118, h138, h5, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h140 | h140
                    · linarith only [h140, h5, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                          · linarith only [h0, h144, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                            · linarith only [h118, h142, h144, h146, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h148 | h148
                              · linarith only [h1, h138, h148, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                                · linarith only [h140, h143, h144, h150, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                                  · linarith only [h1, h118, h142, h144, h152, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h154 | h154
                                    · linarith only [h1, h138, h143, h144, h152, h154, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                                      · linarith only [h140, h143, h144, h156, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                                        · linarith only [h0, h143, h152, h156, h158, h6, hc23, hc34, hlam, hphi]
                                        · linarith only [h1, h118, h158, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                        · linarith only [h143, h5, h6, hc12, hc25, hlam, hphi]
                      · linarith only [h142, h4, h6, hc25, hlam, hphi, ht12, u1ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h163 | h163
              · rcases m.htr 0 3 4 (by decide) (by decide) with h164 | h164
                · linarith only [h164, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                        · linarith only [h0, h169, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                            · linarith only [h164, h166, h168, h169, h172, h2, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                                  · linarith only [h0, h164, h166, h168, h176, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi4]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                                    · linarith only [h168, h169, h178, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h166, h176, h178, h4, h5, hc23, hc34, hlam, hphi]
                                · linarith only [h167, h168, h169, h174, h175, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h166, h174, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
                          · linarith only [h163, h168, h171, h5, hc24, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h168, h4, h5, hc12, hc24, hlam, hphi]
                    · linarith only [h163, h167, h5, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                        · linarith only [h0, h188, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                            · linarith only [h1, h164, h191, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                              · linarith only [h1, h166, h193, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                                  · linarith only [h1, h164, h196, hc23, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                                    · linarith only [h1, h166, h187, h198, hc12, hlam, hphi, u1ehi2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                                        · rcases h0bigk with h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, h163, h166, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u0elo0, u1ehi2]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u0elo0, u1ehi2]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, h163, h166, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u0elo0, u1ehi2]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, h166, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u0elo0, u1ehi2]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h0, hlam, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u0elo1, u1ehi2]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h5, hlam, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, h166, h196, h5, hc34, hlam, hphi, ht12, ht23, p202_1, u1ehi2]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, hlam, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h4, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h164, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h166, hlam, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h2, hlam, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h0, h190, h198, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p202_1, u0elo0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u0elo0, u1ehi2]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, h166, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u0elo0, u1ehi2]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h3, hlam, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h163, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h1, h163, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p202_1, u0elo1, u1ehi2]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h186, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                        · linarith only [h0, h190, h193, h196, h201, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                      · linarith only [h0, h190, h193, h195, h2, h200, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                · linarith only [h186, h195, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                          · linarith only [h163, h190, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                      · linarith only [h187, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h163, h186, h5, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h234 | h234
                · linarith only [h234, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h163, h236, h4, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                        · linarith only [h0, h240, h5, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
                          · linarith only [h0, h163, h242, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
                            · linarith only [h1, h234, h244, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h246 | h246
                              · linarith only [h1, h236, h246, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h248 | h248
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                                  · linarith only [h1, h2, h234, h239, h242, h248, h249, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h251 | h251
                                    · linarith only [h1, h2, h236, h239, h242, h248, h251, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h253 | h253
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h254 | h254
                                        · rcases h0bigk with h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [hlam, p255_0]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h0, h239, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1, u0elo0]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h1, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p255_1, u0elo0, u1ehi2]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h0, h163, h238, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p255_1, u0elo0, u1ehi1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h0, h163, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p255_1, u0elo0, u1ehi1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h0, hlam, p255_1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [hlam, p255_0]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h1, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p255_1, u0elo1, u1ehi2]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h5, hlam, p255_1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h163, hlam, p255_1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h1, hlam, p255_1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h4, hlam, p255_0]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [hlam, p255_0]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h234, hlam, p255_0]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h236, hlam, p255_1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h2, hlam, p255_1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h0, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p255_1, u0elo0, u1ehi1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h1, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p255_1, u0elo0, u1ehi2]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [hlam, p255_0]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h2, h242, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p255_1, u0elo0, u1ehi1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h3, hlam, p255_1]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h1, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p255_1, u0elo4, u1ehi2]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h1, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p255_1, u0elo0, u1ehi2]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [h238, hlam, p255_0]
                                          · have p255_0 := h255c.1
                                            have p255_1 := h255c.2.1
                                            have p255_2 := h255c.2.2.1
                                            have p255_3 := h255c.2.2.2
                                            linarith only [hlam, p255_0]
                                        · linarith only [h2, h248, h249, h254, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                      · linarith only [h2, h248, h253, h5, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h238, h239, h240, h248, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi2]
                      · linarith only [h163, h239, h4, hc12, hc25, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h286 | h286
                        · linarith only [h0, h286, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
                          · linarith only [h1, h163, h288, h4, hc12, hlam, hphi, u1ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h290 | h290
                            · linarith only [h1, h234, h290, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h292 | h292
                              · linarith only [h1, h236, h292, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h294 | h294
                                · linarith only [h2, h238, h294, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                                  · linarith only [h1, h234, h296, hc23, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h298 | h298
                                    · linarith only [h1, h236, h285, h298, hc12, hlam, hphi, u1ehi2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h300 | h300
                                      · linarith only [h1, h238, h300, h4, h5, hc24, hlam, hphi, ht12, u1ehi2]
                                      · linarith only [h1, h300, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h285, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h304 | h304
            · rcases m.htr 0 2 5 (by decide) (by decide) with h305 | h305
              · rcases m.htr 0 3 4 (by decide) (by decide) with h306 | h306
                · rcases m.htr 0 3 5 (by decide) (by decide) with h307 | h307
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h308 | h308
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h309 | h309
                      · linarith only [h0, h309, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h311 | h311
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h312 | h312
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h313 | h313
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h314 | h314
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h316 | h316
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h317 | h317
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h318 | h318
                                      · linarith only [h0, h311, h318, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h1, h309, h311, h315, h316, h318, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · linarith only [h0, h311, h315, h317, h4, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                  · linarith only [h0, h311, h315, h316, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                · linarith only [h308, h315, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                              · linarith only [h307, h309, h311, h314, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi3]
                            · linarith only [h1, h306, h309, h311, h313, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                          · linarith only [h305, h311, h312, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                        · linarith only [h304, h311, h4, hc12, hc23, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h328 | h328
                      · linarith only [h0, h328, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h330 | h330
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h333 | h333
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h334 | h334
                                · linarith only [h0, h308, h330, h334, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h337 | h337
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h338 | h338
                                      · linarith only [h2, h308, h338, hc24, hlam, hphi, ht12, u1ehi3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h340 | h340
                                        · linarith only [h2, h308, h340, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                        · rcases h0bigk with h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [hlam, p342_0]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h0, h331, h334, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo0, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h1, h328, h331, h334, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo0, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo0, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h2, h308, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo0, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h0, hlam, p342_1]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [hlam, p342_0]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h4, hlam, p342_1]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo1, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h2, h308, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo1, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h1, hlam, p342_1]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h0, h331, h334, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo2, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [hlam, p342_0]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h1, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo0, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h1, h2, h308, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo0, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h2, hlam, p342_1]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h304, hlam, p342_0]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h306, hlam, p342_1]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [hlam, p342_0]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h308, hlam, p342_1]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h3, hlam, p342_1]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h305, hlam, p342_0]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h307, hlam, p342_0]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p342_1, u0elo4, u1ehi3]
                                          · have p342_0 := h342c.1
                                            have p342_1 := h342c.2.1
                                            have p342_2 := h342c.2.2.1
                                            have p342_3 := h342c.2.2.2
                                            linarith only [hlam, p342_0]
                                    · linarith only [h0, h331, h334, h337, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                  · linarith only [h0, h331, h334, h336, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h307, h328, h331, h333, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h1, h306, h328, h331, h332, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                          · linarith only [h305, h330, h331, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                        · linarith only [h304, h330, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h305, h307, h4, hlam]
                · linarith only [h304, h306, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h376 | h376
                · rcases m.htr 0 3 5 (by decide) (by decide) with h377 | h377
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h378 | h378
                    · linarith only [h304, h305, h378, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h380 | h380
                      · linarith only [h0, h380, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h382 | h382
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h383 | h383
                          · linarith only [h2, h304, h305, h383, hc12, hlam, hphi, u1ehi3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h385 | h385
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h386 | h386
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h387 | h387
                                · linarith only [h2, h378, h387, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h390 | h390
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h391 | h391
                                      · linarith only [h2, h378, h382, h391, hc12, hlam, hphi, u1ehi3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h393 | h393
                                        · linarith only [h0, h305, h382, h389, h391, h393, hlam]
                                        · rcases h0bigk with h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [hlam, p395_0]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h2, h304, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p395_1, u0elo0, u1ehi3]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h1, h386, hc35, hlam, hphi, ht0b, ht5b, p395_1, u0elo0]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p395_1, u0elo0, u1ehi3]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p395_1, u0elo0, u1ehi4]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h0, hlam, p395_1]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [hlam, p395_0]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h4, hlam, p395_1]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p395_1, u0elo1, u1ehi3]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h305, hlam, p395_1]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h1, hlam, p395_1]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h0, h382, hc24, hlam, hphi, ht0b, ht45, ht5b, p395_1, u0elo2]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [hlam, p395_0]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h1, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p395_1, u0elo0, u1ehi3]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h1, h2, h304, h305, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p395_1, u0elo0, u1ehi3]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h2, hlam, p395_1]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h304, hlam, p395_0]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h376, hlam, p395_1]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [hlam, p395_0]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h378, hlam, p395_1]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h3, hlam, p395_1]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h2, h304, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p395_1, u0elo4, u1ehi3]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h377, hlam, p395_0]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [h1, h2, h377, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p395_1, u0elo0, u1ehi3]
                                          · have p395_0 := h395c.1
                                            have p395_1 := h395c.2.1
                                            have p395_2 := h395c.2.2.1
                                            have p395_3 := h395c.2.2.2
                                            linarith only [hlam, p395_0]
                                    · linarith only [h2, h304, h390, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                  · linarith only [h2, h304, h389, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h377, h385, h386, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h1, h376, h380, h385, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                        · linarith only [h304, h382, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h426 | h426
                    · linarith only [h304, h305, h426, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                      · linarith only [h0, h4, h428, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
                          · linarith only [h2, h304, h305, h431, hc12, hlam, hphi, u1ehi3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h434 | h434
                              · linarith only [h1, h377, h434, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h436 | h436
                                · linarith only [h2, h426, h436, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h438 | h438
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h439 | h439
                                    · linarith only [h2, h304, h377, h4, h439, hc23, hlam, hphi, ht12, u1ehi3]
                                    · linarith only [h2, h304, h4, h439, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                  · linarith only [h2, h304, h4, h438, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                            · linarith only [h376, h377, h428, h433, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4, u1ehi1]
                        · linarith only [h304, h430, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                · linarith only [h304, h376, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h446 | h446
              · rcases m.htr 0 3 4 (by decide) (by decide) with h447 | h447
                · rcases m.htr 0 3 5 (by decide) (by decide) with h448 | h448
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h449 | h449
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
                      · linarith only [h0, h4, h450, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
                        · linarith only [h3, h304, h446, h452, hc12, hlam, hphi, u1ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h454 | h454
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h455 | h455
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h456 | h456
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h457 | h457
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h458 | h458
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h459 | h459
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h460 | h460
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h461 | h461
                                        · linarith only [h1, h455, h461, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                        · linarith only [h2, h457, h461, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                      · linarith only [h1, h3, h304, h446, h455, h457, h460, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                                    · linarith only [h3, h304, h446, h458, h459, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                  · linarith only [h3, h4, h446, h458, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                · linarith only [h447, h449, h457, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi3]
                              · linarith only [h1, h448, h455, h456, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1, h447, h450, h454, h455, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h446, h454, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                    · linarith only [h304, h446, h449, hlam]
                  · linarith only [h4, h446, h448, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h473 | h473
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h474 | h474
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
                      · linarith only [h0, h4, h475, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h477 | h477
                        · linarith only [h3, h304, h446, h477, hc12, hlam, hphi, u1ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h480 | h480
                            · linarith only [h1, h447, h480, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h482 | h482
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h483 | h483
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h484 | h484
                                  · linarith only [h3, h4, h446, h447, h484, hc23, hlam, hphi, ht12, u1ehi4]
                                  · linarith only [h3, h4, h446, h484, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                · linarith only [h474, h480, h482, h483, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                              · linarith only [h473, h475, h479, h482, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h446, h479, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                    · linarith only [h4, h446, h447, h474, hlam]
                  · linarith only [h4, h446, h473, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h492 | h492
                · rcases m.htr 0 3 5 (by decide) (by decide) with h493 | h493
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h494 | h494
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h495 | h495
                      · linarith only [h0, h4, h495, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h497 | h497
                        · linarith only [h0, h304, h497, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h499 | h499
                          · linarith only [h0, h446, h499, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h502 | h502
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h503 | h503
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h504 | h504
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h505 | h505
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h506 | h506
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h507 | h507
                                        · linarith only [h1, h501, h507, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                        · linarith only [h2, h503, h507, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                      · linarith only [h1, h304, h501, h503, h506, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · linarith only [h0, h1, h304, h502, h504, h505, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                                  · linarith only [h0, h4, h504, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h494, h503, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                              · linarith only [h493, h501, h502, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h1, h492, h495, h501, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h516 | h516
                      · linarith only [h0, h4, h516, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h518 | h518
                        · linarith only [h0, h304, h518, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h520 | h520
                          · linarith only [h0, h446, h520, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h522 | h522
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h523 | h523
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h524 | h524
                                · linarith only [h1, h494, h522, h524, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h526 | h526
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h527 | h527
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h528 | h528
                                      · linarith only [h2, h494, h518, h526, h528, hc23, hlam, hphi, ht12, u1ehi1]
                                      · linarith only [h0, h304, h528, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                    · linarith only [h1, h523, h527, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h1, h4, h522, h526, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h493, h522, h523, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h1, h492, h516, h522, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h535 | h535
                    · linarith only [h492, h493, h535, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h537 | h537
                      · linarith only [h0, h4, h537, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h539 | h539
                        · linarith only [h0, h304, h539, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h541 | h541
                          · linarith only [h0, h446, h541, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h543 | h543
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h544 | h544
                              · linarith only [h1, h493, h544, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h546 | h546
                                · linarith only [h2, h535, h546, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h548 | h548
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h549 | h549
                                    · linarith only [h2, h492, h493, h539, h549, hc23, hlam, hphi, ht12, u1ehi1]
                                    · linarith only [h0, h4, h549, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                  · linarith only [h0, h4, h543, h548, hc13, hlam, hphi, u1ehi1]
                            · linarith only [h492, h543, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h554 | h554
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h555 | h555
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h556 | h556
                      · linarith only [h0, h4, h556, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h558 | h558
                        · linarith only [h0, h304, h558, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h560 | h560
                          · linarith only [h0, h446, h560, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h562 | h562
                            · linarith only [h1, h446, h492, h554, h562, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h564 | h564
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h565 | h565
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h566 | h566
                                  · linarith only [h0, h446, h492, h554, h566, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h0, h4, h566, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h555, h565, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                              · linarith only [h554, h564, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
                    · linarith only [h492, h554, h555, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h572 | h572
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h573 | h573
                      · linarith only [h0, h4, h573, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h575 | h575
                        · linarith only [h0, h304, h575, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h577 | h577
                          · linarith only [h0, h446, h577, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h579 | h579
                            · linarith only [h1, h492, h579, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h581 | h581
                              · linarith only [h0, h4, h554, h581, hc13, hlam, hphi, u1ehi1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h583 | h583
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h584 | h584
                                  · linarith only [h0, h4, h492, h584, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h0, h4, h584, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h572, h583, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                      · linarith only [h0, h4, h588, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h590 | h590
                        · linarith only [h0, h304, h590, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h592 | h592
                          · linarith only [h0, h3, h4, h446, h592, hc23, hlam, hphi, ht12, u1ehi4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h594 | h594
                            · linarith only [h1, h4, h492, h594, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h596 | h596
                              · linarith only [h1, h554, h596, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h598 | h598
                                · linarith only [h2, h572, h598, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h600 | h600
                                  · linarith only [h0, h4, h492, h600, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h0, h4, h600, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h606 | h606
    · linarith only [h0, h606, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h608 | h608
      · linarith only [h0, h608, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h610 | h610
        · linarith only [h0, h610, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h612 | h612
          · rcases m.htr 0 2 4 (by decide) (by decide) with h613 | h613
            · rcases m.htr 0 2 5 (by decide) (by decide) with h614 | h614
              · rcases m.htr 0 3 4 (by decide) (by decide) with h615 | h615
                · rcases m.htr 0 3 5 (by decide) (by decide) with h616 | h616
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h617 | h617
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h618 | h618
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h619 | h619
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h620 | h620
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h621 | h621
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h622 | h622
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h623 | h623
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h625 | h625
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h626 | h626
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h627 | h627
                                        · linarith only [h612, h624, h627, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                        · linarith only [h612, h624, h626, h627, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h630 | h630
                                        · linarith only [h612, h615, h626, h630, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                        · rcases h0bigk with h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h0, hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h606, hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h608, hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h610, hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo1, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h606, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo1, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h610, h617, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo1, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h610, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo1, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo2, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h612, hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h610, h617, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo2, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h610, h612, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo1, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo3, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h613, hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h615, hlam, p632_1]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h610, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo3, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u0elo4, u1ehi0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h614, hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h616, hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [h617, hlam, p632_0]
                                          · have p632_0 := h632c.1
                                            have p632_1 := h632c.2.1
                                            have p632_2 := h632c.2.2.1
                                            have p632_3 := h632c.2.2.2
                                            linarith only [hlam, p632_0]
                                    · linarith only [h612, h616, h624, h625, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h659 | h659
                                    · linarith only [h612, h615, h624, h659, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h661 | h661
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h662 | h662
                                        · rcases h0bigk with h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h0, hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h606, hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h608, hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h610, hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p663_1, u0elo1, u1ehi0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h615, h659, h662, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p663_1, u0elo1]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h608, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p663_1, u0elo1, u1ehi0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h610, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p663_1, u0elo1, u1ehi0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p663_1, u0elo2, u1ehi0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h612, hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h608, h612, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p663_1, u0elo1, u1ehi0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h610, h612, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p663_1, u0elo1, u1ehi0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p663_1, u0elo3, u1ehi0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h613, hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h615, hlam, p663_1]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h610, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p663_1, u0elo3, u1ehi0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p663_1, u0elo4, u1ehi0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h614, hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h616, hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [h617, hlam, p663_0]
                                          · have p663_0 := h663c.1
                                            have p663_1 := h663c.2.1
                                            have p663_2 := h663c.2.2.1
                                            have p663_3 := h663c.2.2.2
                                            linarith only [hlam, p663_0]
                                        · linarith only [h612, h615, h617, h624, h662, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h690 | h690
                                        · linarith only [h612, h615, h661, h690, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                        · linarith only [h612, h615, h617, h624, h690, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h608, h617, h623, hlam]
                              · linarith only [h606, h622, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                            · linarith only [h606, h621, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h620, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h0, h619, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h618, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h699 | h699
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h700 | h700
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h701 | h701
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h702 | h702
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h703 | h703
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h704 | h704
                                · linarith only [h608, h617, h699, h702, h704, hc12, hlam, hphi, u1ehi0]
                                · linarith only [h608, h704, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                              · linarith only [h612, h616, h703, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
                            · linarith only [h606, h702, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h614, h701, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                        · linarith only [h0, h613, h700, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi0]
                      · linarith only [h0, h612, h699, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h712 | h712
                    · linarith only [h615, h616, h712, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h714 | h714
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h715 | h715
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h716 | h716
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h717 | h717
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h718 | h718
                              · linarith only [h606, h616, h714, h718, hc12, hlam, hphi, u1ehi0]
                              · linarith only [h606, h718, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                            · linarith only [h606, h615, h717, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi0]
                          · linarith only [h614, h716, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                        · linarith only [h0, h613, h715, hlam]
                      · linarith only [h0, h612, h714, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h725 | h725
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h726 | h726
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h727 | h727
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h728 | h728
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h729 | h729
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h730 | h730
                            · linarith only [h606, h615, h730, hc13, hlam, hphi, u1ehi0]
                            · linarith only [h606, h730, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h608, h614, h728, h729, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                        · linarith only [h0, h613, h728, hlam]
                      · linarith only [h0, h612, h727, hlam]
                    · linarith only [h615, h725, h726, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h737 | h737
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h738 | h738
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h739 | h739
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h740 | h740
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h741 | h741
                            · linarith only [h606, h615, h741, hc13, hlam, hphi, u1ehi0]
                            · linarith only [h606, h741, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h614, h740, hlam]
                        · linarith only [h0, h613, h739, hlam]
                      · linarith only [h0, h612, h738, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h747 | h747
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h748 | h748
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h749 | h749
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h750 | h750
                            · linarith only [h606, h615, h750, hc13, hlam, hphi, u1ehi0]
                            · linarith only [h606, h750, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h614, h749, hlam]
                        · linarith only [h0, h613, h748, hlam]
                      · linarith only [h612, h615, h747, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h756 | h756
                · rcases m.htr 0 3 5 (by decide) (by decide) with h757 | h757
                  · linarith only [h612, h614, h757, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
                    · linarith only [h612, h614, h756, h759, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h762 | h762
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h763 | h763
                          · linarith only [h608, h612, h614, h756, h763, hc12, hlam, hphi, u1ehi0]
                          · linarith only [h0, h763, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h606, h761, h762, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h612, h761, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h768 | h768
                  · linarith only [h612, h614, h768, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h770 | h770
                    · linarith only [h613, h614, h770, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h773 | h773
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h774 | h774
                          · linarith only [h606, h613, h614, h756, h774, hc12, hlam, hphi, u1ehi0]
                          · linarith only [h0, h774, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h606, h613, h772, h773, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                      · linarith only [h0, h612, h614, h772, hc25, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h779 | h779
              · rcases m.htr 0 3 4 (by decide) (by decide) with h780 | h780
                · linarith only [h612, h613, h780, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h782 | h782
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h783 | h783
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h784 | h784
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h785 | h785
                        · linarith only [h0, h613, h785, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h0, h785, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h612, h784, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                    · linarith only [h612, h613, h782, h783, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h790 | h790
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h791 | h791
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h792 | h792
                        · linarith only [h0, h613, h792, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h0, h792, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h612, h613, h791, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h613, h779, h790, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h797 | h797
                · linarith only [h612, h613, h797, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h799 | h799
                  · linarith only [h612, h779, h799, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h801 | h801
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h803 | h803
                        · linarith only [h606, h612, h613, h803, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h0, h803, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h612, h802, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h807 | h807
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h808 | h808
                        · linarith only [h0, h613, h808, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h0, h808, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h612, h807, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h812 | h812
            · rcases m.htr 0 2 5 (by decide) (by decide) with h813 | h813
              · rcases m.htr 0 3 4 (by decide) (by decide) with h814 | h814
                · rcases m.htr 0 3 5 (by decide) (by decide) with h815 | h815
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h816 | h816
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h817 | h817
                      · linarith only [h0, h612, h817, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h817, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h820 | h820
                      · linarith only [h0, h612, h820, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h820, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h612, h813, h815, hlam]
                · linarith only [h612, h812, h814, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h825 | h825
                · rcases m.htr 0 3 5 (by decide) (by decide) with h826 | h826
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h827 | h827
                    · linarith only [h812, h813, h827, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h829 | h829
                      · linarith only [h608, h612, h812, h829, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h829, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h832 | h832
                    · linarith only [h612, h812, h826, h832, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h834 | h834
                      · linarith only [h608, h612, h812, h834, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h834, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h612, h812, h825, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h838 | h838
              · rcases m.htr 0 3 4 (by decide) (by decide) with h839 | h839
                · rcases m.htr 0 3 5 (by decide) (by decide) with h840 | h840
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h841 | h841
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h842 | h842
                      · linarith only [h0, h612, h842, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h842, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h812, h838, h841, hlam]
                  · linarith only [h812, h838, h839, h840, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h847 | h847
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h848 | h848
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h849 | h849
                      · linarith only [h610, h612, h838, h849, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h849, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h612, h838, h839, h848, hlam]
                  · linarith only [h612, h838, h847, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h854 | h854
                · rcases m.htr 0 3 5 (by decide) (by decide) with h855 | h855
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h856 | h856
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h857 | h857
                      · linarith only [h0, h612, h857, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h857, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h860 | h860
                      · linarith only [h0, h612, h860, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h860, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h863 | h863
                    · linarith only [h854, h855, h863, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h865 | h865
                      · linarith only [h0, h612, h865, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h865, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h868 | h868
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h869 | h869
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h870 | h870
                      · linarith only [h0, h612, h870, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h870, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h854, h868, h869, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h874 | h874
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h875 | h875
                      · linarith only [h0, h612, h875, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h875, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                      · linarith only [h0, h612, h878, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h878, hc23, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAA3_M_LI_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 1 5) (by simp) with h8 | h8
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · rcases m.htr 0 1 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h11, h7, hlam]
                  · linarith only [h11, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h10, h5, hlam, p0_1]
              · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
              · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                · rcases m.htr 0 1 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h18, h7, hlam]
                  · linarith only [h18, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h17, h5, hlam, p0_1]
              · linarith only [h16, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h23 | h23
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 4 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h23, h27, hlam]
                    · linarith only [h27, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h26, h7, hlam, p0_1]
                · linarith only [h25, h5, hlam, p0_1]
              · linarith only [h24, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 1 3 (by decide) (by decide) with h34 | h34
                · rcases m.htr 0 1 4 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                      · linarith only [h37, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
                      · linarith only [h37, h5, hlam]
                    · linarith only [h23, h36, hlam, p0_1]
                  · linarith only [h35, h7, hlam, p0_1]
                · linarith only [h34, h5, hlam, p0_1]
              · linarith only [h33, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h45 | h45
    · rcases p0_3 (m.d 1 2) (by simp) with h46 | h46
      · rcases p0_3 (m.d 1 3) (by simp) with h47 | h47
        · linarith only [h47, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h49 | h49
          · rcases p0_3 (m.d 1 5) (by simp) with h50 | h50
            · rcases m.htr 0 1 2 (by decide) (by decide) with h51 | h51
              · linarith only [h46, h51, hlam]
              · linarith only [h51, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h46, h54, hlam]
              · linarith only [h54, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h57 | h57
            · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
              · linarith only [h46, h58, hlam]
              · linarith only [h58, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h61 | h61
              · linarith only [h46, h61, hlam]
              · linarith only [h61, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h64 | h64
        · linarith only [h64, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h66 | h66
          · rcases p0_3 (m.d 1 5) (by simp) with h67 | h67
            · rcases m.htr 0 1 2 (by decide) (by decide) with h68 | h68
              · rcases m.htr 0 1 3 (by decide) (by decide) with h69 | h69
                · rcases m.htr 0 1 4 (by decide) (by decide) with h70 | h70
                  · linarith only [h66, h70, hlam]
                  · linarith only [h46, h70, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h69, hlam, p0_0]
              · linarith only [h46, h68, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 1 3 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
                  · linarith only [h66, h77, hlam]
                  · linarith only [h46, h77, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h76, hlam, p0_0]
              · linarith only [h46, h75, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h82 | h82
            · rcases m.htr 0 1 2 (by decide) (by decide) with h83 | h83
              · rcases m.htr 0 1 3 (by decide) (by decide) with h84 | h84
                · rcases m.htr 0 1 4 (by decide) (by decide) with h85 | h85
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h86 | h86
                    · linarith only [h82, h86, hlam]
                    · linarith only [h46, h86, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h66, h85, hlam, p0_1]
                · linarith only [h84, hlam, p0_0]
              · linarith only [h46, h83, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h92 | h92
              · rcases m.htr 0 1 3 (by decide) (by decide) with h93 | h93
                · rcases m.htr 0 1 4 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h96 | h96
                      · linarith only [h46, h96, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
                        · linarith only [h96, h98, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
                          · linarith only [h100, h96, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                            · linarith only [h102, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                            · linarith only [h102, h66, hlam]
                    · linarith only [h82, h95, hlam, p0_1]
                  · linarith only [h94, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h93, hlam, p0_0]
              · linarith only [h92, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
    · linarith only [h45, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h110 | h110
    · rcases p0_3 (m.d 1 2) (by simp) with h111 | h111
      · rcases p0_3 (m.d 1 3) (by simp) with h112 | h112
        · rcases p0_3 (m.d 1 4) (by simp) with h113 | h113
          · linarith only [h113, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h115 | h115
            · rcases m.htr 0 1 2 (by decide) (by decide) with h116 | h116
              · linarith only [h111, h116, hlam]
              · linarith only [h116, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h119 | h119
              · linarith only [h111, h119, hlam]
              · linarith only [h119, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h122 | h122
          · linarith only [h122, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h124 | h124
            · rcases m.htr 0 1 2 (by decide) (by decide) with h125 | h125
              · linarith only [h111, h125, hlam]
              · linarith only [h112, h125, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h128 | h128
              · linarith only [h111, h128, hlam]
              · linarith only [h112, h128, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h131 | h131
        · linarith only [h111, h131, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h133 | h133
          · linarith only [h133, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h135 | h135
            · rcases m.htr 0 1 2 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 1 3 (by decide) (by decide) with h137 | h137
                · rcases m.htr 0 1 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h139 | h139
                    · linarith only [h135, h139, hlam]
                    · linarith only [h111, h139, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h138, hlam, p0_0]
                · linarith only [h131, h137, hlam, p0_1]
              · linarith only [h111, h136, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h145 | h145
              · rcases m.htr 0 1 3 (by decide) (by decide) with h146 | h146
                · rcases m.htr 0 1 4 (by decide) (by decide) with h147 | h147
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h148 | h148
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h149 | h149
                      · linarith only [h111, h149, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                        · linarith only [h111, h151, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                          · linarith only [h131, h149, h153, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                            · linarith only [h131, h155, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                              · linarith only [h155, h157, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                                · linarith only [h159, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                                · linarith only [h135, h159, hlam]
                    · linarith only [h148, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h147, hlam, p0_0]
                · linarith only [h146, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h111, h145, hlam, p0_1]
    · linarith only [h110, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h167 | h167
    · rcases p0_3 (m.d 1 2) (by simp) with h168 | h168
      · rcases p0_3 (m.d 1 3) (by simp) with h169 | h169
        · rcases p0_3 (m.d 1 4) (by simp) with h170 | h170
          · rcases p0_3 (m.d 1 5) (by simp) with h171 | h171
            · linarith only [h171, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h173 | h173
              · linarith only [h168, h173, hlam]
              · linarith only [h173, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h176 | h176
            · linarith only [h176, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h178 | h178
              · linarith only [h168, h178, hlam]
              · linarith only [h170, h178, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h181 | h181
          · rcases p0_3 (m.d 1 5) (by simp) with h182 | h182
            · linarith only [h182, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h184 | h184
              · linarith only [h168, h184, hlam]
              · linarith only [h169, h184, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h187 | h187
            · linarith only [h187, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h189 | h189
              · linarith only [h168, h189, hlam]
              · linarith only [h169, h189, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h192 | h192
        · linarith only [h168, h192, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h194 | h194
          · rcases p0_3 (m.d 1 5) (by simp) with h195 | h195
            · linarith only [h195, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h197 | h197
              · rcases m.htr 0 1 3 (by decide) (by decide) with h198 | h198
                · rcases m.htr 0 1 4 (by decide) (by decide) with h199 | h199
                  · linarith only [h194, h199, hlam]
                  · linarith only [h168, h199, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h192, h198, hlam, p0_1]
              · linarith only [h168, h197, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h204 | h204
            · linarith only [h204, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h206 | h206
              · rcases m.htr 0 1 3 (by decide) (by decide) with h207 | h207
                · rcases m.htr 0 1 4 (by decide) (by decide) with h208 | h208
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h209 | h209
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
                      · linarith only [h168, h210, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
                        · linarith only [h192, h210, h212, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h214 | h214
                          · linarith only [h168, h214, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h216 | h216
                            · linarith only [h192, h216, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h218 | h218
                              · linarith only [h192, h218, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h220 | h220
                                · linarith only [h194, h220, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                                  · linarith only [h210, h216, h222, hc12, hlam, hphi, ht23, u3elo2]
                                  · linarith only [h210, h222, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h209, hlam, p0_0]
                  · linarith only [h208, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3]
                · linarith only [h194, h207, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h168, h206, hlam, p0_1]
    · linarith only [h167, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h232 | h232
    · rcases p0_3 (m.d 1 2) (by simp) with h233 | h233
      · rcases p0_3 (m.d 1 3) (by simp) with h234 | h234
        · linarith only [h234, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 1 5) (by simp) with h237 | h237
            · rcases m.htr 0 1 2 (by decide) (by decide) with h238 | h238
              · linarith only [h238, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h232, h238, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h241 | h241
              · linarith only [h241, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h232, h241, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h244 | h244
            · rcases m.htr 0 1 2 (by decide) (by decide) with h245 | h245
              · linarith only [h245, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h232, h245, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h248 | h248
              · linarith only [h248, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h232, h248, hlam]
      · linarith only [h233, hlam, p0_0]
    · linarith only [h232, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h253 | h253
    · rcases p0_3 (m.d 1 2) (by simp) with h254 | h254
      · rcases p0_3 (m.d 1 3) (by simp) with h255 | h255
        · rcases p0_3 (m.d 1 4) (by simp) with h256 | h256
          · linarith only [h256, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h258 | h258
            · rcases m.htr 0 1 2 (by decide) (by decide) with h259 | h259
              · linarith only [h259, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h253, h259, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h262 | h262
              · linarith only [h262, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h253, h262, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h265 | h265
          · linarith only [h265, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h267 | h267
            · rcases m.htr 0 1 2 (by decide) (by decide) with h268 | h268
              · linarith only [h255, h268, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h253, h268, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h271 | h271
              · linarith only [h255, h271, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h253, h271, hlam]
      · linarith only [h254, hlam, p0_0]
    · linarith only [h253, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h276 | h276
    · rcases p0_3 (m.d 1 2) (by simp) with h277 | h277
      · rcases p0_3 (m.d 1 3) (by simp) with h278 | h278
        · rcases p0_3 (m.d 1 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 1 5) (by simp) with h280 | h280
            · linarith only [h280, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h282 | h282
              · linarith only [h282, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h276, h282, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h285 | h285
            · linarith only [h285, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h287 | h287
              · linarith only [h279, h287, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h276, h287, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h290 | h290
          · rcases p0_3 (m.d 1 5) (by simp) with h291 | h291
            · linarith only [h291, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h293 | h293
              · linarith only [h278, h293, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h276, h293, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h296 | h296
            · linarith only [h296, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h298 | h298
              · linarith only [h278, h298, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h276, h298, hlam]
      · linarith only [h277, hlam, p0_0]
    · linarith only [h276, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h306 | h306
    · rcases p0_3 (m.d 1 2) (by simp) with h307 | h307
      · rcases p0_3 (m.d 1 3) (by simp) with h308 | h308
        · rcases p0_3 (m.d 1 4) (by simp) with h309 | h309
          · linarith only [h309, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h311 | h311
            · rcases m.htr 0 1 2 (by decide) (by decide) with h312 | h312
              · linarith only [h307, h312, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h306, h312, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h315 | h315
              · linarith only [h307, h315, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h306, h315, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h308, hlam, p0_0]
      · linarith only [h307, hc12, hlam, hphi, ht23, p0_1, u3elo1]
    · linarith only [h306, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h321 | h321
    · rcases p0_3 (m.d 1 2) (by simp) with h322 | h322
      · rcases p0_3 (m.d 1 3) (by simp) with h323 | h323
        · rcases p0_3 (m.d 1 4) (by simp) with h324 | h324
          · rcases p0_3 (m.d 1 5) (by simp) with h325 | h325
            · linarith only [h325, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h327 | h327
              · linarith only [h322, h327, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h321, h327, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h330 | h330
            · linarith only [h330, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h332 | h332
              · linarith only [h322, h324, h332, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h321, h324, h332, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h323, hlam, p0_0]
      · linarith only [h322, hc12, hlam, hphi, ht23, p0_1, u3elo1]
    · linarith only [h321, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h339 | h339
    · rcases p0_3 (m.d 1 2) (by simp) with h340 | h340
      · linarith only [h340, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h342 | h342
        · linarith only [h342, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h344 | h344
          · rcases p0_3 (m.d 1 5) (by simp) with h345 | h345
            · rcases m.htr 0 1 2 (by decide) (by decide) with h346 | h346
              · rcases m.htr 0 1 3 (by decide) (by decide) with h347 | h347
                · rcases m.htr 0 1 4 (by decide) (by decide) with h348 | h348
                  · linarith only [h348, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h339, h348, hlam]
                · linarith only [h342, h347, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h339, h346, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h353 | h353
              · rcases m.htr 0 1 3 (by decide) (by decide) with h354 | h354
                · rcases m.htr 0 1 4 (by decide) (by decide) with h355 | h355
                  · linarith only [h355, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h339, h355, hlam]
                · linarith only [h342, h354, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h339, h353, hlam, p0_1]
          · linarith only [h344, hlam, p0_0]
    · linarith only [h339, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h362 | h362
    · rcases p0_3 (m.d 1 2) (by simp) with h363 | h363
      · rcases p0_3 (m.d 1 3) (by simp) with h364 | h364
        · linarith only [h364, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h366 | h366
          · rcases p0_3 (m.d 1 5) (by simp) with h367 | h367
            · rcases m.htr 0 1 2 (by decide) (by decide) with h368 | h368
              · linarith only [h363, h368, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h362, h368, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h371 | h371
              · linarith only [h363, h371, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h362, h371, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h366, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h375 | h375
        · linarith only [h375, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h377 | h377
          · rcases p0_3 (m.d 1 5) (by simp) with h378 | h378
            · rcases m.htr 0 1 2 (by decide) (by decide) with h379 | h379
              · rcases m.htr 0 1 3 (by decide) (by decide) with h380 | h380
                · rcases m.htr 0 1 4 (by decide) (by decide) with h381 | h381
                  · linarith only [h363, h381, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h362, h381, hlam]
                · linarith only [h380, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h362, h363, h379, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h386 | h386
              · rcases m.htr 0 1 3 (by decide) (by decide) with h387 | h387
                · rcases m.htr 0 1 4 (by decide) (by decide) with h388 | h388
                  · linarith only [h363, h388, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h362, h388, hlam]
                · linarith only [h387, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h362, h363, h386, hlam, p0_1]
          · linarith only [h377, hlam, p0_0]
    · linarith only [h362, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h396 | h396
    · rcases p0_3 (m.d 1 2) (by simp) with h397 | h397
      · rcases p0_3 (m.d 1 3) (by simp) with h398 | h398
        · rcases p0_3 (m.d 1 4) (by simp) with h399 | h399
          · rcases p0_3 (m.d 1 5) (by simp) with h400 | h400
            · linarith only [h400, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h402 | h402
              · linarith only [h397, h402, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h396, h402, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · linarith only [h399, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h406 | h406
          · rcases p0_3 (m.d 1 5) (by simp) with h407 | h407
            · linarith only [h407, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h409 | h409
              · linarith only [h397, h398, h409, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h396, h398, h409, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h406, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h413 | h413
        · linarith only [h397, h413, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h415 | h415
          · rcases p0_3 (m.d 1 5) (by simp) with h416 | h416
            · linarith only [h416, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h418 | h418
              · rcases m.htr 0 1 3 (by decide) (by decide) with h419 | h419
                · rcases m.htr 0 1 4 (by decide) (by decide) with h420 | h420
                  · linarith only [h397, h420, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h396, h420, hlam]
                · linarith only [h413, h419, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h396, h397, h418, hlam, p0_1]
          · linarith only [h415, hlam, p0_0]
    · linarith only [h396, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h428 | h428
    · rcases p0_3 (m.d 1 2) (by simp) with h429 | h429
      · linarith only [h429, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h431 | h431
        · linarith only [h431, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h433 | h433
          · rcases p0_3 (m.d 1 5) (by simp) with h434 | h434
            · rcases m.htr 0 1 2 (by decide) (by decide) with h435 | h435
              · rcases m.htr 0 1 3 (by decide) (by decide) with h436 | h436
                · rcases m.htr 0 1 4 (by decide) (by decide) with h437 | h437
                  · linarith only [h433, h437, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h428, h437, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h428, h431, h436, hlam, p0_1]
              · linarith only [h428, h435, hlam, p0_1]
            · linarith only [h434, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h443 | h443
            · rcases m.htr 0 1 2 (by decide) (by decide) with h444 | h444
              · rcases m.htr 0 1 3 (by decide) (by decide) with h445 | h445
                · rcases m.htr 0 1 4 (by decide) (by decide) with h446 | h446
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h447 | h447
                    · linarith only [h447, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h428, h447, hlam]
                  · linarith only [h433, h446, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h428, h431, h445, hlam, p0_1]
              · linarith only [h428, h444, hlam, p0_1]
            · linarith only [h443, hlam, p0_0]
    · linarith only [h428, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h455 | h455
    · rcases p0_3 (m.d 1 2) (by simp) with h456 | h456
      · rcases p0_3 (m.d 1 3) (by simp) with h457 | h457
        · linarith only [h457, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h459 | h459
          · rcases p0_3 (m.d 1 5) (by simp) with h460 | h460
            · rcases m.htr 0 1 2 (by decide) (by decide) with h461 | h461
              · linarith only [h456, h461, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h455, h461, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h460, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h465 | h465
            · rcases m.htr 0 1 2 (by decide) (by decide) with h466 | h466
              · linarith only [h456, h466, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h455, h466, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h465, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h470 | h470
        · linarith only [h470, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h472 | h472
          · rcases p0_3 (m.d 1 5) (by simp) with h473 | h473
            · rcases m.htr 0 1 2 (by decide) (by decide) with h474 | h474
              · rcases m.htr 0 1 3 (by decide) (by decide) with h475 | h475
                · rcases m.htr 0 1 4 (by decide) (by decide) with h476 | h476
                  · linarith only [h456, h472, h476, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h455, h456, h476, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h455, h475, hlam, p0_1]
              · linarith only [h455, h456, h474, hlam, p0_1]
            · linarith only [h473, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h482 | h482
            · rcases m.htr 0 1 2 (by decide) (by decide) with h483 | h483
              · rcases m.htr 0 1 3 (by decide) (by decide) with h484 | h484
                · rcases m.htr 0 1 4 (by decide) (by decide) with h485 | h485
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h486 | h486
                    · linarith only [h456, h486, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h455, h486, hlam]
                  · linarith only [h472, h485, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h455, h484, hlam, p0_1]
              · linarith only [h455, h456, h483, hlam, p0_1]
            · linarith only [h482, hlam, p0_0]
    · linarith only [h455, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h494 | h494
    · rcases p0_3 (m.d 1 2) (by simp) with h495 | h495
      · rcases p0_3 (m.d 1 3) (by simp) with h496 | h496
        · rcases p0_3 (m.d 1 4) (by simp) with h497 | h497
          · linarith only [h497, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h499 | h499
            · rcases m.htr 0 1 2 (by decide) (by decide) with h500 | h500
              · linarith only [h495, h500, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h494, h500, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h499, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h504 | h504
          · linarith only [h504, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h506 | h506
            · rcases m.htr 0 1 2 (by decide) (by decide) with h507 | h507
              · linarith only [h495, h496, h507, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h494, h496, h507, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h506, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h511 | h511
        · linarith only [h495, h511, hc12, hlam, hphi, ht23, p0_1, u3elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h513 | h513
          · linarith only [h513, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h515 | h515
            · rcases m.htr 0 1 2 (by decide) (by decide) with h516 | h516
              · rcases m.htr 0 1 3 (by decide) (by decide) with h517 | h517
                · rcases m.htr 0 1 4 (by decide) (by decide) with h518 | h518
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h519 | h519
                    · linarith only [h495, h519, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h494, h519, hlam]
                  · linarith only [h518, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h494, h511, h517, hlam, p0_1]
              · linarith only [h494, h495, h516, hlam, p0_1]
            · linarith only [h515, hlam, p0_0]
    · linarith only [h494, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LI_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
                · linarith only [h5, h9, hlam]
                · linarith only [h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h8, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h13 | h13
              · rcases m.htr 0 1 3 (by decide) (by decide) with h14 | h14
                · linarith only [h14, h5, hlam]
                · linarith only [h14, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h13, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h18 | h18
            · rcases m.htr 0 1 2 (by decide) (by decide) with h19 | h19
              · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
                · linarith only [h20, h5, hlam]
                · linarith only [h20, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h19, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                · linarith only [h25, h5, hlam]
                · linarith only [h25, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h24, hlam, p0_0]
        · linarith only [h5, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · rcases p0_3 (m.d 1 2) (by simp) with h33 | h33
      · rcases p0_3 (m.d 1 3) (by simp) with h34 | h34
        · rcases p0_3 (m.d 1 4) (by simp) with h35 | h35
          · linarith only [h35, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h37 | h37
            · rcases m.htr 0 1 2 (by decide) (by decide) with h38 | h38
              · linarith only [h33, h38, hlam]
              · linarith only [h38, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h41 | h41
              · linarith only [h33, h41, hlam]
              · linarith only [h41, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h34, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h45 | h45
        · rcases p0_3 (m.d 1 4) (by simp) with h46 | h46
          · linarith only [h46, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h48 | h48
            · rcases m.htr 0 1 2 (by decide) (by decide) with h49 | h49
              · rcases m.htr 0 1 3 (by decide) (by decide) with h50 | h50
                · linarith only [h45, h50, hlam]
                · linarith only [h33, h50, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h33, h49, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · rcases m.htr 0 1 3 (by decide) (by decide) with h55 | h55
                · linarith only [h45, h55, hlam]
                · linarith only [h33, h55, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h33, h54, hlam, p0_1]
        · linarith only [h45, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
    · linarith only [h32, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h61 | h61
    · rcases p0_3 (m.d 1 2) (by simp) with h62 | h62
      · rcases p0_3 (m.d 1 3) (by simp) with h63 | h63
        · rcases p0_3 (m.d 1 4) (by simp) with h64 | h64
          · rcases p0_3 (m.d 1 5) (by simp) with h65 | h65
            · linarith only [h65, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h67 | h67
              · linarith only [h62, h67, hlam]
              · linarith only [h67, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h70 | h70
            · linarith only [h70, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h72 | h72
              · linarith only [h62, h72, hlam]
              · linarith only [h64, h72, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h63, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h76 | h76
        · rcases p0_3 (m.d 1 4) (by simp) with h77 | h77
          · rcases p0_3 (m.d 1 5) (by simp) with h78 | h78
            · linarith only [h78, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h80 | h80
              · rcases m.htr 0 1 3 (by decide) (by decide) with h81 | h81
                · linarith only [h76, h81, hlam]
                · linarith only [h62, h81, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h62, h80, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h85 | h85
            · linarith only [h85, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
              · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                · linarith only [h76, h88, hlam]
                · linarith only [h62, h88, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h62, h87, hlam, p0_1]
        · linarith only [h76, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
    · linarith only [h61, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h97 | h97
    · rcases p0_3 (m.d 1 2) (by simp) with h98 | h98
      · rcases p0_3 (m.d 1 3) (by simp) with h99 | h99
        · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
          · linarith only [h100, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h102 | h102
            · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
              · linarith only [h103, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h103, h97, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
              · linarith only [h106, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h106, h97, hlam]
        · linarith only [h99, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1, u3ehi1]
      · linarith only [h98, hlam, p0_0]
    · linarith only [h97, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h112 | h112
    · rcases p0_3 (m.d 1 2) (by simp) with h113 | h113
      · rcases p0_3 (m.d 1 3) (by simp) with h114 | h114
        · rcases p0_3 (m.d 1 4) (by simp) with h115 | h115
          · rcases p0_3 (m.d 1 5) (by simp) with h116 | h116
            · linarith only [h116, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · linarith only [h118, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h112, h118, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h121 | h121
            · linarith only [h121, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h123 | h123
              · linarith only [h115, h123, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h112, h123, hlam]
        · linarith only [h114, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1, u3ehi1]
      · linarith only [h113, hlam, p0_0]
    · linarith only [h112, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h130 | h130
    · rcases p0_3 (m.d 1 2) (by simp) with h131 | h131
      · linarith only [h131, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h133 | h133
        · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
          · rcases p0_3 (m.d 1 5) (by simp) with h135 | h135
            · rcases m.htr 0 1 2 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 1 3 (by decide) (by decide) with h137 | h137
                · linarith only [h137, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h130, h137, hlam]
              · linarith only [h136, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · rcases m.htr 0 1 3 (by decide) (by decide) with h142 | h142
                · linarith only [h142, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h130, h142, hlam]
              · linarith only [h141, hc01, hlam, hphi, p0_1, u1elo2]
          · rcases p0_3 (m.d 1 5) (by simp) with h146 | h146
            · rcases m.htr 0 1 2 (by decide) (by decide) with h147 | h147
              · rcases m.htr 0 1 3 (by decide) (by decide) with h148 | h148
                · linarith only [h148, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h130, h148, hlam]
              · linarith only [h147, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h152 | h152
              · rcases m.htr 0 1 3 (by decide) (by decide) with h153 | h153
                · linarith only [h153, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h130, h153, hlam]
              · linarith only [h152, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h133, hlam, p0_0]
    · linarith only [h130, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 2) (by simp) with h161 | h161
      · rcases p0_3 (m.d 1 3) (by simp) with h162 | h162
        · rcases p0_3 (m.d 1 4) (by simp) with h163 | h163
          · linarith only [h163, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h165 | h165
            · rcases m.htr 0 1 2 (by decide) (by decide) with h166 | h166
              · linarith only [h161, h166, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h160, h166, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h169 | h169
              · linarith only [h161, h169, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h160, h169, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h162, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h173 | h173
        · rcases p0_3 (m.d 1 4) (by simp) with h174 | h174
          · linarith only [h174, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h176 | h176
            · rcases m.htr 0 1 2 (by decide) (by decide) with h177 | h177
              · rcases m.htr 0 1 3 (by decide) (by decide) with h178 | h178
                · linarith only [h161, h178, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h160, h178, hlam]
              · linarith only [h161, h177, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h182 | h182
              · rcases m.htr 0 1 3 (by decide) (by decide) with h183 | h183
                · linarith only [h161, h183, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h160, h183, hlam]
              · linarith only [h161, h182, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h173, hlam, p0_0]
    · linarith only [h160, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h189 | h189
    · rcases p0_3 (m.d 1 2) (by simp) with h190 | h190
      · rcases p0_3 (m.d 1 3) (by simp) with h191 | h191
        · rcases p0_3 (m.d 1 4) (by simp) with h192 | h192
          · rcases p0_3 (m.d 1 5) (by simp) with h193 | h193
            · linarith only [h193, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h195 | h195
              · linarith only [h190, h195, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h189, h195, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h198 | h198
            · linarith only [h198, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
              · linarith only [h190, h192, h200, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h189, h192, h200, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h191, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h204 | h204
        · rcases p0_3 (m.d 1 4) (by simp) with h205 | h205
          · rcases p0_3 (m.d 1 5) (by simp) with h206 | h206
            · linarith only [h206, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h208 | h208
              · rcases m.htr 0 1 3 (by decide) (by decide) with h209 | h209
                · linarith only [h190, h209, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h189, h209, hlam]
              · linarith only [h190, h208, hc01, hlam, hphi, p0_1, u1elo2]
          · rcases p0_3 (m.d 1 5) (by simp) with h213 | h213
            · linarith only [h213, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h215 | h215
              · rcases m.htr 0 1 3 (by decide) (by decide) with h216 | h216
                · linarith only [h190, h216, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h189, h216, hlam]
              · linarith only [h190, h215, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h204, hlam, p0_0]
    · linarith only [h189, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h223 | h223
    · rcases p0_3 (m.d 1 2) (by simp) with h224 | h224
      · linarith only [h224, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h226 | h226
        · rcases p0_3 (m.d 1 4) (by simp) with h227 | h227
          · rcases p0_3 (m.d 1 5) (by simp) with h228 | h228
            · rcases m.htr 0 1 2 (by decide) (by decide) with h229 | h229
              · rcases m.htr 0 1 3 (by decide) (by decide) with h230 | h230
                · linarith only [h226, h230, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h223, h230, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h223, h229, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
              · rcases m.htr 0 1 3 (by decide) (by decide) with h235 | h235
                · linarith only [h226, h235, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h223, h235, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h223, h234, hlam, p0_1]
          · linarith only [h227, hlam, p0_0]
        · linarith only [h223, h226, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
    · linarith only [h223, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo3, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h244 | h244
    · rcases p0_3 (m.d 1 2) (by simp) with h245 | h245
      · rcases p0_3 (m.d 1 3) (by simp) with h246 | h246
        · rcases p0_3 (m.d 1 4) (by simp) with h247 | h247
          · rcases p0_3 (m.d 1 5) (by simp) with h248 | h248
            · linarith only [h248, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h250 | h250
              · linarith only [h245, h250, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h244, h250, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · linarith only [h247, hlam, p0_0]
        · linarith only [h244, h246, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h255 | h255
        · rcases p0_3 (m.d 1 4) (by simp) with h256 | h256
          · rcases p0_3 (m.d 1 5) (by simp) with h257 | h257
            · linarith only [h257, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h259 | h259
              · rcases m.htr 0 1 3 (by decide) (by decide) with h260 | h260
                · linarith only [h245, h255, h260, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h244, h245, h260, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h244, h245, h259, hlam, p0_1]
          · linarith only [h256, hlam, p0_0]
        · linarith only [h244, h255, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
    · linarith only [h244, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 2) (by simp) with h269 | h269
      · linarith only [h269, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h271 | h271
        · rcases p0_3 (m.d 1 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 1 5) (by simp) with h273 | h273
            · rcases m.htr 0 1 2 (by decide) (by decide) with h274 | h274
              · rcases m.htr 0 1 3 (by decide) (by decide) with h275 | h275
                · linarith only [h271, h275, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h268, h275, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h268, h274, hlam, p0_1]
            · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h280 | h280
            · rcases m.htr 0 1 2 (by decide) (by decide) with h281 | h281
              · rcases m.htr 0 1 3 (by decide) (by decide) with h282 | h282
                · linarith only [h271, h282, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h268, h282, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h268, h281, hlam, p0_1]
            · linarith only [h280, hlam, p0_0]
        · linarith only [h268, h271, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
    · linarith only [h268, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo4, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h290 | h290
    · rcases p0_3 (m.d 1 2) (by simp) with h291 | h291
      · rcases p0_3 (m.d 1 3) (by simp) with h292 | h292
        · rcases p0_3 (m.d 1 4) (by simp) with h293 | h293
          · linarith only [h293, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h295 | h295
            · rcases m.htr 0 1 2 (by decide) (by decide) with h296 | h296
              · linarith only [h291, h296, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h290, h296, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h295, hlam, p0_0]
        · linarith only [h290, h292, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h301 | h301
        · rcases p0_3 (m.d 1 4) (by simp) with h302 | h302
          · linarith only [h302, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h304 | h304
            · rcases m.htr 0 1 2 (by decide) (by decide) with h305 | h305
              · rcases m.htr 0 1 3 (by decide) (by decide) with h306 | h306
                · linarith only [h291, h301, h306, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h290, h291, h306, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h290, h291, h305, hlam, p0_1]
            · linarith only [h304, hlam, p0_0]
        · linarith only [h290, h301, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
    · linarith only [h290, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h3, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h11, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h15, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h18, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
              · linarith only [h21, h3, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h23 | h23
                · linarith only [h23, h4, h5, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h25, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h25, h3, h5, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h28 | h28
            · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h31, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h3, h31, h4, hc12, hc24, hlam, hphi]
                · linarith only [h29, h3, h30, h4, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h35 | h35
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
                  · linarith only [h0, h36, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h3, h36, h4, hc12, hc24, hlam, hphi]
                · linarith only [h3, h35, h4, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
              · linarith only [h28, h3, h40, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
                · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                  · linarith only [h0, h43, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h28, h3, h43, hc25, hlam, hphi, ht12, u1ehi1]
                · linarith only [h3, h4, h42, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h47 | h47
          · rcases m.htr 0 2 5 (by decide) (by decide) with h48 | h48
            · rcases m.htr 0 3 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 0 4 5 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                  · linarith only [h3, h47, h50, h51, hc12, hlam, hphi, ht01, u0ehi9]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                      · linarith only [h1, h54, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · linarith only [h49, h51, h53, h54, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi4]
                    · linarith only [h48, h53, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                  · linarith only [h3, h58, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h61 | h61
                      · linarith only [h1, h61, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · linarith only [h1, h49, h58, h60, h61, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                    · linarith only [h3, h48, h60, hc12, hc23, hlam, hphi]
              · linarith only [h3, h48, h49, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h66 | h66
              · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                · linarith only [h47, h48, h67, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                  · linarith only [h0, h69, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                    · linarith only [h1, h48, h69, h71, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
                      · linarith only [h1, h73, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · linarith only [h66, h69, h73, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
                · linarith only [h47, h48, h76, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                  · linarith only [h3, h47, h78, hc12, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h1, h47, h48, h78, h80, hlam, hphi, u0ehi8, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                      · linarith only [h1, h82, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                        · linarith only [h2, h76, h78, h82, h84, hc14, hlam, hphi, u0ehi8, u0elo0, u1ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                          · linarith only [h3, h47, h66, h86, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h2, h3, h78, h82, h86, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h89 | h89
            · rcases m.htr 0 3 5 (by decide) (by decide) with h90 | h90
              · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
                · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                  · linarith only [h3, h89, h92, hc12, hlam, hphi, ht01, u0ehi9]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                      · linarith only [h1, h95, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · linarith only [h90, h92, h94, h95, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi4]
                    · linarith only [h89, h94, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                · linarith only [h47, h89, h91, hlam]
              · linarith only [h3, h89, h90, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h101 | h101
              · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
                · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                  · linarith only [h0, h103, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                    · linarith only [h1, h103, h105, h89, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                      · linarith only [h1, h107, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · linarith only [h101, h103, h107, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
                  · linarith only [h110, h3, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                    · linarith only [h1, h110, h112, h89, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                      · linarith only [h1, h114, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · linarith only [h1, h101, h110, h114, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
                · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                  · linarith only [h118, h3, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
                    · linarith only [h1, h118, h120, h89, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h122 | h122
                      · linarith only [h1, h101, h122, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                            · linarith only [h101, h126, h3, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                            · linarith only [h125, h126, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h118, h122, h125, h2, h3, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                        · linarith only [h117, h124, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
                  · linarith only [h131, h3, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                    · linarith only [h1, h131, h133, h89, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                      · linarith only [h1, h135, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                        · linarith only [h117, h131, h135, h137, h2, hc14, hlam, hphi, u0ehi8, u0elo0, u1ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h139 | h139
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                            · linarith only [h101, h131, h135, h140, h2, h3, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                            · linarith only [h139, h140, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h131, h135, h139, h2, h3, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h146 | h146
    · linarith only [h0, h146, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h148 | h148
      · linarith only [h0, h148, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h150 | h150
        · rcases m.htr 0 2 4 (by decide) (by decide) with h151 | h151
          · rcases m.htr 0 2 5 (by decide) (by decide) with h152 | h152
            · rcases m.htr 0 3 5 (by decide) (by decide) with h153 | h153
              · rcases m.htr 0 4 5 (by decide) (by decide) with h154 | h154
                · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                          · linarith only [h150, h159, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h161 | h161
                            · linarith only [h151, h159, h161, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                            · linarith only [h153, h161, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                        · linarith only [h154, h158, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                      · linarith only [h150, h153, h157, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                    · linarith only [h152, h156, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                  · linarith only [h0, h155, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                        · linarith only [h154, h171, hc14, hlam, hphi, ht01, u0ehi8]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                          · linarith only [h150, h173, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                            · linarith only [h151, h173, h175, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                            · linarith only [h150, h153, h175, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                      · linarith only [h150, h153, h170, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                    · linarith only [h146, h152, h168, h169, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h0, h168, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h181 | h181
                · rcases m.htr 1 2 3 (by decide) (by decide) with h182 | h182
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                      · linarith only [h146, h153, h182, h184, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h146, h184, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h152, h183, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                  · linarith only [h0, h150, h182, hlam, hphi, u0ehi5, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h191 | h191
                      · linarith only [h146, h153, h189, h191, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h146, h191, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h152, h190, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                  · linarith only [h0, h150, h189, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h196 | h196
              · linarith only [h150, h152, h196, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h198 | h198
                · linarith only [h151, h152, h198, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h150, h152, h201, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h201, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h150, h200, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h205 | h205
            · rcases m.htr 0 3 5 (by decide) (by decide) with h206 | h206
              · rcases m.htr 0 4 5 (by decide) (by decide) with h207 | h207
                · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h211 | h211
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                          · linarith only [h150, h151, h212, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h150, h151, h212, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h207, h211, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi3]
                      · linarith only [h150, h151, h206, h210, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h146, h151, h205, h208, h209, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h150, h151, h208, hc12, hc24, hlam, hphi]
                · linarith only [h150, h151, h207, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h220 | h220
                · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
                      · linarith only [h206, h221, h223, hc12, hlam, hphi, ht01, u0ehi7]
                      · linarith only [h146, h223, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h151, h205, h222, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h221, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h150, h151, h220, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h229 | h229
              · linarith only [h150, h205, h229, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h231 | h231
                · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h233 | h233
                    · linarith only [h150, h205, h233, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h233, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h150, h232, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h150, h151, h231, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h238 | h238
          · rcases m.htr 0 2 5 (by decide) (by decide) with h239 | h239
            · rcases m.htr 0 3 5 (by decide) (by decide) with h240 | h240
              · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
                · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                  · linarith only [h148, h150, h238, h241, h242, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h242, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h245 | h245
                  · linarith only [h150, h245, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h245, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h150, h239, h240, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h249 | h249
              · rcases m.htr 0 4 5 (by decide) (by decide) with h250 | h250
                · linarith only [h238, h239, h250, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h252 | h252
                  · linarith only [h150, h252, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h252, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h255 | h255
                · linarith only [h150, h238, h249, h255, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h257 | h257
                  · linarith only [h150, h238, h257, hc12, hlam, hphi, ht01, u0ehi8]
                  · linarith only [h0, h257, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h260 | h260
            · rcases m.htr 0 3 5 (by decide) (by decide) with h261 | h261
              · rcases m.htr 0 4 5 (by decide) (by decide) with h262 | h262
                · rcases m.htr 1 2 3 (by decide) (by decide) with h263 | h263
                  · linarith only [h148, h150, h260, h263, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h263, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h238, h260, h262, hlam]
              · linarith only [h150, h260, h261, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
              · rcases m.htr 0 4 5 (by decide) (by decide) with h269 | h269
                · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
                  · linarith only [h0, h150, h270, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h270, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h273 | h273
                  · linarith only [h0, h150, h273, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h273, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h276 | h276
                · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
                  · linarith only [h0, h150, h277, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h277, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h280 | h280
                  · linarith only [h0, h150, h280, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h280, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem n7l_sAA3_M_LR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h3elo := hb3.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h10, h5, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h13, h5, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h16, h7, h8, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h18, h8, hc13, hlam, hphi, u3elo2]
                      · rcases h1bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h18, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20_1, u1elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1, u1elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          rcases p20_3 (m.d 0 1) (by simp) with h24 | h24
                          · rcases p20_3 (m.d 1 2) (by simp) with h25 | h25
                            · linarith only [h0, h25, hlam]
                            · linarith only [h18, h25, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20_1, u1elo0]
                          · linarith only [h24, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h7, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1, u1elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h0, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1, u1elo1]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1, u1elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h0, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1, u1elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h1, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h5, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h8, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p20_1, u3elo4]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h8, hlam, p20_1]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h2, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p20_1, u1elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h7, hlam, p20_1]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h16, hlam, p20_1]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h3, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h6, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20_1, u1elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h0, h6, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1, u1elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                      · linarith only [h0, h5, h52, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h50, h52, h7, hc23, hlam, hphi, u3elo3]
                    · linarith only [h50, h51, h7, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                      · linarith only [h50, h57, hc13, hlam, hphi, u3elo2]
                      · rcases h1bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p59_1, u1elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          rcases p59_3 (m.d 0 1) (by simp) with h62 | h62
                          · rcases p59_3 (m.d 1 2) (by simp) with h63 | h63
                            · linarith only [h0, h63, hlam]
                            · linarith only [h5, h63, hlam]
                          · linarith only [h62, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h56, hc45, hlam, hphi, ht01, ht0b, ht5b, p59_1, u1elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          rcases p59_3 (m.d 0 1) (by simp) with h68 | h68
                          · rcases p59_3 (m.d 1 2) (by simp) with h69 | h69
                            · linarith only [h0, h69, hlam]
                            · linarith only [h6, h69, hlam]
                          · linarith only [h68, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h0, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h0, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p59_1, u1elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h0, h56, hc45, hlam, hphi, ht01, ht0b, ht5b, p59_1, u1elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h0, h5, h50, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p59_1, u1elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h1, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h5, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h7, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h50, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h2, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p59_1, u1elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p59_1, u1elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h2, h5, h50, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p59_1, u1elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h3, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h6, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p59_1, u1elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h56, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h93 | h93
                      · linarith only [h0, h5, h50, h56, h93, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases h1bigk with h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          rcases p95_3 (m.d 0 1) (by simp) with h98 | h98
                          · rcases p95_3 (m.d 1 2) (by simp) with h99 | h99
                            · linarith only [h0, h99, hlam]
                            · linarith only [h5, h99, hlam]
                          · linarith only [h98, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          rcases p95_3 (m.d 0 1) (by simp) with h103 | h103
                          · rcases p95_3 (m.d 1 2) (by simp) with h104 | h104
                            · linarith only [h0, h104, hlam]
                            · linarith only [h104, h6, h93, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                          · linarith only [h103, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          rcases p95_3 (m.d 0 1) (by simp) with h108 | h108
                          · rcases p95_3 (m.d 1 2) (by simp) with h109 | h109
                            · linarith only [h0, h109, hlam]
                            · linarith only [h109, h6, hlam]
                          · linarith only [h108, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h1, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h5, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h7, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h50, hlam, p95_1]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h2, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h56, hc12, hc45, hlam, hphi, ht23, ht34, p95_1]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, h5, h56, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h56, hlam, p95_1]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h3, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h6, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, h6, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                  · linarith only [h134, h5, h6, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                    · linarith only [h133, h134, h136, h5, h6, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                      · linarith only [h134, h138, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h138, h5, h6, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h141 | h141
                  · linarith only [h133, h141, h5, h6, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h144 | h144
                      · linarith only [h141, h144, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h144, h5, h6, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
                      · linarith only [h0, h147, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h147, h5, h6, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
              · linarith only [h0, h150, h4, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                      · rcases h1bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          rcases p156_3 (m.d 0 1) (by simp) with h158 | h158
                          · rcases p156_3 (m.d 1 2) (by simp) with h159 | h159
                            · linarith only [h159, hlam, p156_0]
                            · rcases p156_3 (m.d 1 3) (by simp) with h161 | h161
                              · linarith only [h1, h161, hlam]
                              · linarith only [h161, h5, hlam]
                          · linarith only [h158, hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h152, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p156_1, u1elo0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h154, hc45, hlam, hphi, ht01, ht0b, ht5b, p156_1, u1elo0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          rcases p156_3 (m.d 0 1) (by simp) with h167 | h167
                          · rcases p156_3 (m.d 1 2) (by simp) with h168 | h168
                            · linarith only [h0, h168, hlam]
                            · rcases p156_3 (m.d 1 3) (by simp) with h170 | h170
                              · linarith only [h1, h170, hlam]
                              · linarith only [h153, h170, hlam]
                          · linarith only [h167, hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h0, hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h5, hlam, p156_1]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h0, h150, h154, h155, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p156_1, u1elo0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h150, hlam, p156_1]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h1, hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, p156_1, u3elo1]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h0, h154, h4, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p156_1, u1elo0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h0, h4, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p156_1, u1elo0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h2, hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p156_1, u1elo0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h152, hlam, p156_1]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h150, h152, hc12, hlam, hphi, ht23, p156_1, u3elo1]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h3, hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p156_1, u1elo0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h153, hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [h154, hlam, p156_0]
                        · have p156_0 := h156c.1
                          have p156_1 := h156c.2.1
                          have p156_2 := h156c.2.2.1
                          have p156_3 := h156c.2.2.2
                          linarith only [hlam, p156_0]
                      · linarith only [h153, h155, h5, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h195 | h195
                      · rcases h1bigk with h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          rcases p196_3 (m.d 0 1) (by simp) with h198 | h198
                          · rcases p196_3 (m.d 1 2) (by simp) with h199 | h199
                            · linarith only [h199, hlam, p196_0]
                            · rcases p196_3 (m.d 1 3) (by simp) with h201 | h201
                              · linarith only [h1, h201, hlam]
                              · linarith only [h201, h5, hlam]
                          · linarith only [h198, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h153, hc35, hlam, hphi, ht01, ht0b, ht5b, p196_1, u1elo0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          rcases p196_3 (m.d 0 1) (by simp) with h206 | h206
                          · rcases p196_3 (m.d 1 2) (by simp) with h207 | h207
                            · linarith only [h0, h207, hlam]
                            · rcases p196_3 (m.d 1 3) (by simp) with h209 | h209
                              · linarith only [h1, h209, hlam]
                              · linarith only [h152, h209, hlam]
                          · linarith only [h206, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          rcases p196_3 (m.d 0 1) (by simp) with h213 | h213
                          · rcases p196_3 (m.d 1 2) (by simp) with h214 | h214
                            · linarith only [h0, h214, hlam]
                            · rcases p196_3 (m.d 1 3) (by simp) with h216 | h216
                              · linarith only [h1, h216, hlam]
                              · linarith only [h153, h216, hlam]
                          · linarith only [h213, hlam, p196_0]
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
                          linarith only [h5, hlam, p196_1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p196_1, u1elo0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h150, hlam, p196_1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h1, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, p196_1, u3elo1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, h4, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p196_1, u1elo0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, h4, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p196_1, u1elo0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h2, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h154, hc12, hc45, hlam, hphi, ht23, ht34, p196_1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h152, hlam, p196_1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h154, hlam, p196_1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h3, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p196_1, u1elo0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h153, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, h150, h195, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p196_1, u1elo0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hlam, p196_0]
                      · linarith only [h195, h5, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h241 | h241
                    · linarith only [h152, h153, h241, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h243 | h243
                      · linarith only [h153, h243, hc13, hlam, hphi, u3elo2]
                      · linarith only [h243, h5, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h246 | h246
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                      · rcases h1bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          rcases p249_3 (m.d 0 1) (by simp) with h251 | h251
                          · rcases p249_3 (m.d 1 2) (by simp) with h252 | h252
                            · linarith only [h252, hlam, p249_0]
                            · rcases p249_3 (m.d 1 3) (by simp) with h254 | h254
                              · linarith only [h1, h254, hlam]
                              · linarith only [h254, h5, hlam]
                          · linarith only [h251, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h246, hc35, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h152, h246, hc35, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          rcases p249_3 (m.d 0 1) (by simp) with h260 | h260
                          · rcases p249_3 (m.d 1 2) (by simp) with h261 | h261
                            · linarith only [h0, h261, hlam]
                            · rcases p249_3 (m.d 1 3) (by simp) with h263 | h263
                              · linarith only [h1, h263, hlam]
                              · linarith only [h246, h263, hlam]
                          · linarith only [h260, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h0, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h5, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h152, h246, hc35, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h150, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h1, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h152, hc12, hlam, hphi, ht23, p249_1, u3elo3]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h152, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h0, h150, h152, h248, h4, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht5b, p249_1, u1elo0, u3elo3]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h2, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h150, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h3, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p249_1, u1elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h246, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h247, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                      · linarith only [h248, h5, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h152, h246, h247, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h290 | h290
                      · linarith only [h0, h246, h290, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h290, h5, hc12, hlam, hphi, ht23, u3elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                      · linarith only [h246, h293, h5, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h293, h5, hc12, hlam, hphi, ht23, u3elo4]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]
        · linarith only [h3, hlam, hphi, ht01, u0ehi5, u1elo4]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi6, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

end R2N4
