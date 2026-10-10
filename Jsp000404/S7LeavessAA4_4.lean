import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAA4_H_I_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
          · linarith only [h6, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h8 | h8
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h5, hlam]
                · linarith only [h10, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h14 | h14
              · rcases m.htr 0 1 3 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h5, hlam]
                · linarith only [h15, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h14, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h19 | h19
          · linarith only [h19, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h21 | h21
            · rcases m.htr 0 1 2 (by decide) (by decide) with h22 | h22
              · rcases m.htr 0 1 3 (by decide) (by decide) with h23 | h23
                · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h21, h25, hlam]
                    · linarith only [h25, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h19, h24, hlam, p0_1]
                · linarith only [h23, h5, hlam, p0_1]
              · linarith only [h22, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h31 | h31
              · rcases m.htr 0 1 3 (by decide) (by decide) with h32 | h32
                · rcases m.htr 0 1 4 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
                        · linarith only [h36, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · linarith only [h36, h5, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                        · linarith only [h39, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · linarith only [h39, h5, hlam]
                    · linarith only [h21, h34, hlam, p0_1]
                  · linarith only [h19, h33, hlam, p0_1]
                · linarith only [h32, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h31, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h47 | h47
    · rcases p0_3 (m.d 1 2) (by simp) with h48 | h48
      · rcases p0_3 (m.d 1 3) (by simp) with h49 | h49
        · linarith only [h49, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h51 | h51
          · linarith only [h51, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h48, h54, hlam]
              · linarith only [h54, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h57 | h57
              · linarith only [h48, h57, hlam]
              · linarith only [h57, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h60 | h60
        · linarith only [h60, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h62 | h62
          · linarith only [h48, h62, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h64 | h64
            · rcases m.htr 0 1 2 (by decide) (by decide) with h65 | h65
              · rcases m.htr 0 1 3 (by decide) (by decide) with h66 | h66
                · rcases m.htr 0 1 4 (by decide) (by decide) with h67 | h67
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h68 | h68
                    · linarith only [h64, h68, hlam]
                    · linarith only [h48, h68, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h62, h67, hlam, p0_1]
                · linarith only [h66, hlam, p0_0]
              · linarith only [h48, h65, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h74 | h74
              · rcases m.htr 0 1 3 (by decide) (by decide) with h75 | h75
                · rcases m.htr 0 1 4 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                        · linarith only [h48, h79, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                          · linarith only [h79, h81, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                            · linarith only [h79, h83, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                              · linarith only [h85, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h62, h85, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
                        · linarith only [h48, h88, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                          · linarith only [h88, h90, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
                            · linarith only [h88, h92, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                              · linarith only [h94, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h62, h94, hlam]
                    · linarith only [h64, h77, hlam, p0_1]
                  · linarith only [h76, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h75, hlam, p0_0]
              · linarith only [h74, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
    · linarith only [h47, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h102 | h102
    · rcases p0_3 (m.d 1 2) (by simp) with h103 | h103
      · rcases p0_3 (m.d 1 3) (by simp) with h104 | h104
        · rcases p0_3 (m.d 1 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h107 | h107
            · rcases m.htr 0 1 2 (by decide) (by decide) with h108 | h108
              · linarith only [h103, h108, hlam]
              · linarith only [h108, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h111 | h111
              · linarith only [h103, h111, hlam]
              · linarith only [h111, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h116 | h116
            · rcases m.htr 0 1 2 (by decide) (by decide) with h117 | h117
              · linarith only [h103, h117, hlam]
              · linarith only [h104, h117, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h120 | h120
              · linarith only [h103, h120, hlam]
              · linarith only [h104, h120, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h123 | h123
        · rcases p0_3 (m.d 1 4) (by simp) with h124 | h124
          · linarith only [h124, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h126 | h126
            · rcases m.htr 0 1 2 (by decide) (by decide) with h127 | h127
              · rcases m.htr 0 1 3 (by decide) (by decide) with h128 | h128
                · linarith only [h123, h128, hlam]
                · linarith only [h103, h128, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h103, h127, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h132 | h132
              · rcases m.htr 0 1 3 (by decide) (by decide) with h133 | h133
                · linarith only [h123, h133, hlam]
                · linarith only [h103, h133, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h103, h132, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h137 | h137
          · linarith only [h137, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h139 | h139
            · rcases m.htr 0 1 2 (by decide) (by decide) with h140 | h140
              · rcases m.htr 0 1 3 (by decide) (by decide) with h141 | h141
                · rcases m.htr 0 1 4 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h143 | h143
                    · linarith only [h139, h143, hlam]
                    · linarith only [h103, h143, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h142, hlam, p0_0]
                · linarith only [h123, h141, hlam, p0_1]
              · linarith only [h103, h140, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h149 | h149
              · rcases m.htr 0 1 3 (by decide) (by decide) with h150 | h150
                · rcases m.htr 0 1 4 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                        · linarith only [h103, h154, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                          · linarith only [h103, h156, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h158 | h158
                            · linarith only [h123, h154, h158, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                              · linarith only [h123, h160, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                                · linarith only [h160, h162, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                                  · linarith only [h164, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                  · linarith only [h139, h164, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
                        · linarith only [h103, h167, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                          · linarith only [h103, h169, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                            · linarith only [h123, h167, h171, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                              · linarith only [h123, h173, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
                                · linarith only [h173, h175, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
                                  · linarith only [h153, h177, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                  · linarith only [h139, h177, hlam]
                    · linarith only [h152, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h151, hlam, p0_0]
                · linarith only [h150, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h103, h149, hlam, p0_1]
    · linarith only [h102, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h185 | h185
    · rcases p0_3 (m.d 1 2) (by simp) with h186 | h186
      · rcases p0_3 (m.d 1 3) (by simp) with h187 | h187
        · rcases p0_3 (m.d 1 4) (by simp) with h188 | h188
          · linarith only [h188, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h190 | h190
            · linarith only [h190, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h192 | h192
              · linarith only [h186, h192, hlam]
              · linarith only [h188, h192, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h195 | h195
          · linarith only [h187, h195, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h197 | h197
            · linarith only [h197, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h199 | h199
              · linarith only [h186, h199, hlam]
              · linarith only [h187, h199, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h202 | h202
        · rcases p0_3 (m.d 1 4) (by simp) with h203 | h203
          · linarith only [h186, h203, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h205 | h205
            · linarith only [h205, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h207 | h207
              · rcases m.htr 0 1 3 (by decide) (by decide) with h208 | h208
                · linarith only [h202, h208, hlam]
                · linarith only [h186, h208, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h186, h207, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h212 | h212
          · linarith only [h186, h212, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h214 | h214
            · linarith only [h214, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h216 | h216
              · rcases m.htr 0 1 3 (by decide) (by decide) with h217 | h217
                · rcases m.htr 0 1 4 (by decide) (by decide) with h218 | h218
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h219 | h219
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h220 | h220
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                        · linarith only [h186, h221, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
                          · linarith only [h202, h221, h223, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h225 | h225
                            · linarith only [h186, h225, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                              · linarith only [h202, h227, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                                · linarith only [h202, h229, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                                  · linarith only [h212, h231, hlam]
                                  · linarith only [h220, h221, h227, h231, hc12, hlam, hphi, ht23, ht34, u4elo0]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                        · linarith only [h186, h234, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h236 | h236
                          · linarith only [h202, h234, h236, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
                            · linarith only [h186, h238, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
                              · linarith only [h202, h240, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                                · linarith only [h202, h242, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                                  · linarith only [h212, h244, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                                    · linarith only [h220, h246, hc04, hlam, hphi, u4elo2]
                                    · linarith only [h236, h246, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h219, hlam, p0_0]
                  · linarith only [h218, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                · linarith only [h212, h217, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h186, h216, hlam, p0_1]
    · linarith only [h185, hlam, p0_0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h256 | h256
    · rcases p0_3 (m.d 1 2) (by simp) with h257 | h257
      · rcases p0_3 (m.d 1 3) (by simp) with h258 | h258
        · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h260 | h260
          · linarith only [h260, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h262 | h262
            · rcases m.htr 0 1 2 (by decide) (by decide) with h263 | h263
              · linarith only [h263, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h256, h263, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h266 | h266
              · linarith only [h266, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h256, h266, hlam]
      · linarith only [h257, hlam, p0_0]
    · linarith only [h256, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h271 | h271
    · rcases p0_3 (m.d 1 2) (by simp) with h272 | h272
      · rcases p0_3 (m.d 1 3) (by simp) with h273 | h273
        · rcases p0_3 (m.d 1 4) (by simp) with h274 | h274
          · linarith only [h274, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h276 | h276
            · rcases m.htr 0 1 2 (by decide) (by decide) with h277 | h277
              · linarith only [h277, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h271, h277, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h280 | h280
              · linarith only [h280, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h271, h280, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h283 | h283
          · linarith only [h283, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h285 | h285
            · rcases m.htr 0 1 2 (by decide) (by decide) with h286 | h286
              · linarith only [h273, h286, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h271, h286, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h289 | h289
              · linarith only [h273, h289, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h271, h289, hlam]
      · linarith only [h272, hlam, p0_0]
    · linarith only [h271, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h294 | h294
    · rcases p0_3 (m.d 1 2) (by simp) with h295 | h295
      · rcases p0_3 (m.d 1 3) (by simp) with h296 | h296
        · rcases p0_3 (m.d 1 4) (by simp) with h297 | h297
          · linarith only [h297, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h299 | h299
            · linarith only [h299, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h301 | h301
              · linarith only [h297, h301, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h294, h301, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h304 | h304
          · linarith only [h296, h304, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h306 | h306
            · linarith only [h306, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h308 | h308
              · linarith only [h296, h308, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h294, h308, hlam]
      · linarith only [h295, hlam, p0_0]
    · linarith only [h294, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h314 | h314
    · rcases p0_3 (m.d 1 2) (by simp) with h315 | h315
      · linarith only [h315, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h317 | h317
        · rcases p0_3 (m.d 1 4) (by simp) with h318 | h318
          · linarith only [h318, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h320 | h320
            · rcases m.htr 0 1 2 (by decide) (by decide) with h321 | h321
              · rcases m.htr 0 1 3 (by decide) (by decide) with h322 | h322
                · linarith only [h322, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h314, h322, hlam]
              · linarith only [h321, hc01, hc13, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h326 | h326
              · rcases m.htr 0 1 3 (by decide) (by decide) with h327 | h327
                · linarith only [h327, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h314, h327, hlam]
              · linarith only [h326, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h317, hlam, p0_0]
    · linarith only [h314, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h334 | h334
    · rcases p0_3 (m.d 1 2) (by simp) with h335 | h335
      · rcases p0_3 (m.d 1 3) (by simp) with h336 | h336
        · rcases p0_3 (m.d 1 4) (by simp) with h337 | h337
          · linarith only [h337, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h339 | h339
            · rcases m.htr 0 1 2 (by decide) (by decide) with h340 | h340
              · linarith only [h335, h340, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h334, h340, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h343 | h343
              · linarith only [h335, h343, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h334, h343, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h336, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h347 | h347
        · rcases p0_3 (m.d 1 4) (by simp) with h348 | h348
          · linarith only [h348, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h350 | h350
            · rcases m.htr 0 1 2 (by decide) (by decide) with h351 | h351
              · rcases m.htr 0 1 3 (by decide) (by decide) with h352 | h352
                · linarith only [h335, h352, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h334, h352, hlam]
              · linarith only [h335, h351, hc01, hc13, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h356 | h356
              · rcases m.htr 0 1 3 (by decide) (by decide) with h357 | h357
                · linarith only [h335, h357, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h334, h357, hlam]
              · linarith only [h335, h356, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h347, hlam, p0_0]
    · linarith only [h334, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h363 | h363
    · rcases p0_3 (m.d 1 2) (by simp) with h364 | h364
      · rcases p0_3 (m.d 1 3) (by simp) with h365 | h365
        · rcases p0_3 (m.d 1 4) (by simp) with h366 | h366
          · linarith only [h366, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h368 | h368
            · linarith only [h368, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h370 | h370
              · linarith only [h364, h366, h370, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h363, h366, h370, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h365, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h374 | h374
        · rcases p0_3 (m.d 1 4) (by simp) with h375 | h375
          · linarith only [h364, h375, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h377 | h377
            · linarith only [h377, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h379 | h379
              · rcases m.htr 0 1 3 (by decide) (by decide) with h380 | h380
                · linarith only [h364, h380, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h363, h380, hlam]
              · linarith only [h364, h379, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h374, hlam, p0_0]
    · linarith only [h363, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h392 | h392
    · rcases p0_3 (m.d 1 2) (by simp) with h393 | h393
      · linarith only [h393, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h395 | h395
        · rcases p0_3 (m.d 1 4) (by simp) with h396 | h396
          · linarith only [h396, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h398 | h398
            · rcases m.htr 0 1 2 (by decide) (by decide) with h399 | h399
              · rcases m.htr 0 1 3 (by decide) (by decide) with h400 | h400
                · linarith only [h395, h400, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h392, h400, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h392, h399, hlam, p0_1]
            · linarith only [h398, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h405 | h405
          · linarith only [h405, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h407 | h407
            · rcases m.htr 0 1 2 (by decide) (by decide) with h408 | h408
              · rcases m.htr 0 1 3 (by decide) (by decide) with h409 | h409
                · rcases m.htr 0 1 4 (by decide) (by decide) with h410 | h410
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h411 | h411
                    · linarith only [h411, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h392, h411, hlam]
                  · linarith only [h405, h410, hc01, hc15, hlam, hphi, p0_1]
                · linarith only [h392, h395, h409, hlam, p0_1]
              · linarith only [h392, h408, hlam, p0_1]
            · linarith only [h407, hlam, p0_0]
    · linarith only [h392, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h419 | h419
    · rcases p0_3 (m.d 1 2) (by simp) with h420 | h420
      · rcases p0_3 (m.d 1 3) (by simp) with h421 | h421
        · linarith only [h421, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h423 | h423
          · linarith only [h423, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h425 | h425
            · rcases m.htr 0 1 2 (by decide) (by decide) with h426 | h426
              · linarith only [h420, h426, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h419, h426, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h425, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h430 | h430
        · linarith only [h430, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h432 | h432
          · linarith only [h420, h432, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h434 | h434
            · rcases m.htr 0 1 2 (by decide) (by decide) with h435 | h435
              · rcases m.htr 0 1 3 (by decide) (by decide) with h436 | h436
                · rcases m.htr 0 1 4 (by decide) (by decide) with h437 | h437
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h438 | h438
                    · linarith only [h420, h438, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h419, h438, hlam]
                  · linarith only [h432, h437, hc01, hc15, hlam, hphi, p0_1]
                · linarith only [h419, h436, hlam, p0_1]
              · linarith only [h419, h420, h435, hlam, p0_1]
            · linarith only [h434, hlam, p0_0]
    · linarith only [h419, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h446 | h446
    · rcases p0_3 (m.d 1 2) (by simp) with h447 | h447
      · rcases p0_3 (m.d 1 3) (by simp) with h448 | h448
        · rcases p0_3 (m.d 1 4) (by simp) with h449 | h449
          · linarith only [h449, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h451 | h451
            · rcases m.htr 0 1 2 (by decide) (by decide) with h452 | h452
              · linarith only [h447, h452, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h446, h452, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h451, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h456 | h456
          · linarith only [h456, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h458 | h458
            · rcases m.htr 0 1 2 (by decide) (by decide) with h459 | h459
              · linarith only [h447, h448, h459, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h446, h448, h459, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h458, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h463 | h463
        · rcases p0_3 (m.d 1 4) (by simp) with h464 | h464
          · linarith only [h464, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h466 | h466
            · rcases m.htr 0 1 2 (by decide) (by decide) with h467 | h467
              · rcases m.htr 0 1 3 (by decide) (by decide) with h468 | h468
                · linarith only [h447, h463, h468, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h446, h447, h468, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h446, h447, h467, hlam, p0_1]
            · linarith only [h466, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h473 | h473
          · linarith only [h473, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h475 | h475
            · rcases m.htr 0 1 2 (by decide) (by decide) with h476 | h476
              · rcases m.htr 0 1 3 (by decide) (by decide) with h477 | h477
                · rcases m.htr 0 1 4 (by decide) (by decide) with h478 | h478
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h479 | h479
                    · linarith only [h447, h479, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h446, h479, hlam]
                  · linarith only [h478, hc01, hc15, hlam, hphi, p0_1]
                · linarith only [h446, h463, h477, hlam, p0_1]
              · linarith only [h446, h447, h476, hlam, p0_1]
            · linarith only [h475, hlam, p0_0]
    · linarith only [h446, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_H_I_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
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
          · linarith only [h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h19 | h19
          · rcases p0_3 (m.d 1 5) (by simp) with h20 | h20
            · rcases m.htr 0 1 2 (by decide) (by decide) with h21 | h21
              · rcases m.htr 0 1 3 (by decide) (by decide) with h22 | h22
                · rcases m.htr 0 1 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h19, h23, hlam]
                  · linarith only [h23, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h22, h5, hlam, p0_1]
              · linarith only [h21, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h28 | h28
              · rcases m.htr 0 1 3 (by decide) (by decide) with h29 | h29
                · rcases m.htr 0 1 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h19, h30, hlam]
                  · linarith only [h30, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h29, h5, hlam, p0_1]
              · linarith only [h28, hlam, p0_0]
          · linarith only [h19, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · rcases p0_3 (m.d 1 2) (by simp) with h38 | h38
      · rcases p0_3 (m.d 1 3) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h41 | h41
          · rcases p0_3 (m.d 1 5) (by simp) with h42 | h42
            · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
              · linarith only [h38, h43, hlam]
              · linarith only [h43, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h46 | h46
              · linarith only [h38, h46, hlam]
              · linarith only [h46, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h41, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h50 | h50
        · linarith only [h50, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h52 | h52
          · rcases p0_3 (m.d 1 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · rcases m.htr 0 1 3 (by decide) (by decide) with h55 | h55
                · rcases m.htr 0 1 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h52, h56, hlam]
                  · linarith only [h38, h56, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h55, hlam, p0_0]
              · linarith only [h38, h54, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h61 | h61
              · rcases m.htr 0 1 3 (by decide) (by decide) with h62 | h62
                · rcases m.htr 0 1 4 (by decide) (by decide) with h63 | h63
                  · linarith only [h52, h63, hlam]
                  · linarith only [h38, h63, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h62, hlam, p0_0]
              · linarith only [h38, h61, hlam, p0_1]
          · linarith only [h52, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
    · linarith only [h37, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h71 | h71
    · rcases p0_3 (m.d 1 2) (by simp) with h72 | h72
      · rcases p0_3 (m.d 1 3) (by simp) with h73 | h73
        · rcases p0_3 (m.d 1 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 1 5) (by simp) with h75 | h75
            · linarith only [h75, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h77 | h77
              · linarith only [h72, h77, hlam]
              · linarith only [h77, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · linarith only [h74, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h81 | h81
          · rcases p0_3 (m.d 1 5) (by simp) with h82 | h82
            · linarith only [h82, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h84 | h84
              · linarith only [h72, h84, hlam]
              · linarith only [h73, h84, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h81, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h88 | h88
        · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
          · rcases p0_3 (m.d 1 5) (by simp) with h90 | h90
            · linarith only [h90, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h92 | h92
              · rcases m.htr 0 1 3 (by decide) (by decide) with h93 | h93
                · linarith only [h88, h93, hlam]
                · linarith only [h72, h93, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h72, h92, hlam, p0_1]
          · linarith only [h89, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h98 | h98
          · rcases p0_3 (m.d 1 5) (by simp) with h99 | h99
            · linarith only [h99, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h101 | h101
              · rcases m.htr 0 1 3 (by decide) (by decide) with h102 | h102
                · rcases m.htr 0 1 4 (by decide) (by decide) with h103 | h103
                  · linarith only [h103, h98, hlam]
                  · linarith only [h103, h88, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h102, h72, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h101, h72, hlam, p0_1]
          · linarith only [h98, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
    · linarith only [h71, hlam, p0_0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h112 | h112
    · rcases p0_3 (m.d 1 2) (by simp) with h113 | h113
      · rcases p0_3 (m.d 1 3) (by simp) with h114 | h114
        · linarith only [h114, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 1 5) (by simp) with h117 | h117
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · linarith only [h118, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h118, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · linarith only [h121, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h121, hlam]
          · linarith only [h116, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
      · linarith only [h113, hlam, p0_0]
    · linarith only [h112, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h128 | h128
    · rcases p0_3 (m.d 1 2) (by simp) with h129 | h129
      · rcases p0_3 (m.d 1 3) (by simp) with h130 | h130
        · rcases p0_3 (m.d 1 4) (by simp) with h131 | h131
          · rcases p0_3 (m.d 1 5) (by simp) with h132 | h132
            · linarith only [h132, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
              · linarith only [h134, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h128, h134, hlam]
          · linarith only [h131, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 1 5) (by simp) with h139 | h139
            · linarith only [h139, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · linarith only [h130, h141, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h128, h141, hlam]
          · linarith only [h138, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
      · linarith only [h129, hlam, p0_0]
    · linarith only [h128, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h148 | h148
    · rcases p0_3 (m.d 1 2) (by simp) with h149 | h149
      · linarith only [h149, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h151 | h151
        · rcases p0_3 (m.d 1 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 1 5) (by simp) with h153 | h153
            · rcases m.htr 0 1 2 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 1 3 (by decide) (by decide) with h155 | h155
                · linarith only [h155, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h148, h155, hlam]
              · linarith only [h154, hc01, hc13, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h159 | h159
              · rcases m.htr 0 1 3 (by decide) (by decide) with h160 | h160
                · linarith only [h160, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h148, h160, hlam]
              · linarith only [h159, hc01, hc13, hlam, hphi, p0_1]
          · linarith only [h152, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
        · linarith only [h151, hlam, p0_0]
    · linarith only [h148, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h169 | h169
    · rcases p0_3 (m.d 1 2) (by simp) with h170 | h170
      · rcases p0_3 (m.d 1 3) (by simp) with h171 | h171
        · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
          · rcases p0_3 (m.d 1 5) (by simp) with h173 | h173
            · linarith only [h173, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h175 | h175
              · linarith only [h170, h175, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h169, h175, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · linarith only [h169, h172, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
        · linarith only [h171, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h180 | h180
        · rcases p0_3 (m.d 1 4) (by simp) with h181 | h181
          · rcases p0_3 (m.d 1 5) (by simp) with h182 | h182
            · linarith only [h182, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h184 | h184
              · rcases m.htr 0 1 3 (by decide) (by decide) with h185 | h185
                · linarith only [h170, h185, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h169, h185, hlam]
              · linarith only [h170, h184, hc01, hc13, hlam, hphi, p0_1]
          · linarith only [h181, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
        · linarith only [h180, hlam, p0_0]
    · linarith only [h169, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h193 | h193
    · rcases p0_3 (m.d 1 2) (by simp) with h194 | h194
      · linarith only [h194, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h196 | h196
        · rcases p0_3 (m.d 1 4) (by simp) with h197 | h197
          · rcases p0_3 (m.d 1 5) (by simp) with h198 | h198
            · rcases m.htr 0 1 2 (by decide) (by decide) with h199 | h199
              · rcases m.htr 0 1 3 (by decide) (by decide) with h200 | h200
                · linarith only [h196, h200, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h193, h200, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h193, h199, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h204 | h204
              · rcases m.htr 0 1 3 (by decide) (by decide) with h205 | h205
                · linarith only [h196, h205, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h193, h205, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h193, h204, hlam, p0_1]
          · linarith only [h197, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h210 | h210
          · rcases p0_3 (m.d 1 5) (by simp) with h211 | h211
            · rcases m.htr 0 1 2 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 1 3 (by decide) (by decide) with h213 | h213
                · rcases m.htr 0 1 4 (by decide) (by decide) with h214 | h214
                  · linarith only [h214, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h193, h214, hlam]
                · linarith only [h196, h213, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h193, h212, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h219 | h219
              · rcases m.htr 0 1 3 (by decide) (by decide) with h220 | h220
                · rcases m.htr 0 1 4 (by decide) (by decide) with h221 | h221
                  · linarith only [h221, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h193, h221, hlam]
                · linarith only [h196, h220, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h193, h219, hlam, p0_1]
          · linarith only [h210, hlam, p0_0]
    · linarith only [h193, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h228 | h228
    · rcases p0_3 (m.d 1 2) (by simp) with h229 | h229
      · rcases p0_3 (m.d 1 3) (by simp) with h230 | h230
        · linarith only [h230, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h232 | h232
          · rcases p0_3 (m.d 1 5) (by simp) with h233 | h233
            · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
              · linarith only [h229, h234, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h228, h234, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h237 | h237
              · linarith only [h229, h237, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h228, h237, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h232, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h241 | h241
        · linarith only [h241, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h243 | h243
          · rcases p0_3 (m.d 1 5) (by simp) with h244 | h244
            · rcases m.htr 0 1 2 (by decide) (by decide) with h245 | h245
              · rcases m.htr 0 1 3 (by decide) (by decide) with h246 | h246
                · rcases m.htr 0 1 4 (by decide) (by decide) with h247 | h247
                  · linarith only [h229, h247, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h228, h247, hlam]
                · linarith only [h246, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h228, h229, h245, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h252 | h252
              · rcases m.htr 0 1 3 (by decide) (by decide) with h253 | h253
                · rcases m.htr 0 1 4 (by decide) (by decide) with h254 | h254
                  · linarith only [h229, h254, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h228, h254, hlam]
                · linarith only [h253, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h228, h252, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h243, hlam, p0_0]
    · linarith only [h228, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h262 | h262
    · rcases p0_3 (m.d 1 2) (by simp) with h263 | h263
      · rcases p0_3 (m.d 1 3) (by simp) with h264 | h264
        · rcases p0_3 (m.d 1 4) (by simp) with h265 | h265
          · rcases p0_3 (m.d 1 5) (by simp) with h266 | h266
            · linarith only [h266, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h268 | h268
              · linarith only [h263, h268, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h262, h268, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · linarith only [h265, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 1 5) (by simp) with h273 | h273
            · linarith only [h273, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h275 | h275
              · linarith only [h263, h264, h275, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h262, h264, h275, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h279 | h279
        · rcases p0_3 (m.d 1 4) (by simp) with h280 | h280
          · rcases p0_3 (m.d 1 5) (by simp) with h281 | h281
            · linarith only [h281, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h283 | h283
              · rcases m.htr 0 1 3 (by decide) (by decide) with h284 | h284
                · linarith only [h263, h279, h284, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h262, h263, h284, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h262, h263, h283, hlam, p0_1]
          · linarith only [h280, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h289 | h289
          · rcases p0_3 (m.d 1 5) (by simp) with h290 | h290
            · linarith only [h290, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h292 | h292
              · rcases m.htr 0 1 3 (by decide) (by decide) with h293 | h293
                · rcases m.htr 0 1 4 (by decide) (by decide) with h294 | h294
                  · linarith only [h263, h294, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h262, h294, hlam]
                · linarith only [h279, h293, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h262, h263, h292, hlam, p0_1]
          · linarith only [h289, hlam, p0_0]
    · linarith only [h262, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h302 | h302
    · rcases p0_3 (m.d 1 2) (by simp) with h303 | h303
      · linarith only [h303, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h305 | h305
        · rcases p0_3 (m.d 1 4) (by simp) with h306 | h306
          · rcases p0_3 (m.d 1 5) (by simp) with h307 | h307
            · rcases m.htr 0 1 2 (by decide) (by decide) with h308 | h308
              · rcases m.htr 0 1 3 (by decide) (by decide) with h309 | h309
                · linarith only [h305, h309, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h309, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h302, h308, hlam, p0_1]
            · linarith only [h307, hlam, p0_0]
          · linarith only [h302, h306, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h315 | h315
          · rcases p0_3 (m.d 1 5) (by simp) with h316 | h316
            · rcases m.htr 0 1 2 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 1 3 (by decide) (by decide) with h318 | h318
                · rcases m.htr 0 1 4 (by decide) (by decide) with h319 | h319
                  · linarith only [h315, h319, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h302, h319, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h318, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h302, h317, hlam, p0_1]
            · linarith only [h316, hlam, p0_0]
          · linarith only [h302, h315, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
    · linarith only [h302, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h327 | h327
    · rcases p0_3 (m.d 1 2) (by simp) with h328 | h328
      · rcases p0_3 (m.d 1 3) (by simp) with h329 | h329
        · linarith only [h329, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h331 | h331
          · rcases p0_3 (m.d 1 5) (by simp) with h332 | h332
            · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
              · linarith only [h328, h333, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h327, h333, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h332, hlam, p0_0]
          · linarith only [h327, h331, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h338 | h338
        · linarith only [h338, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h340 | h340
          · rcases p0_3 (m.d 1 5) (by simp) with h341 | h341
            · rcases m.htr 0 1 2 (by decide) (by decide) with h342 | h342
              · rcases m.htr 0 1 3 (by decide) (by decide) with h343 | h343
                · rcases m.htr 0 1 4 (by decide) (by decide) with h344 | h344
                  · linarith only [h328, h340, h344, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h327, h328, h344, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h327, h343, hlam, p0_1]
              · linarith only [h327, h328, h342, hlam, p0_1]
            · linarith only [h341, hlam, p0_0]
          · linarith only [h327, h340, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
    · linarith only [h327, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_H_I_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h2, h3, hlam, ht01, u1elo0]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA4_H_I_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases h0emin with h4 | h4 | h4 | h4 | h4
          · linarith only [h4, hlam, ht01, u1elo0]
          · linarith only [h0, h4, hlam, ht01, u1elo0]
          · linarith only [h1, h4, hlam, ht01, u1elo0]
          · linarith only [h2, h4, hlam, ht01, u1elo0]
          · linarith only [h3, h4, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA4_H_I_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo3]

theorem n7l_sAA4_H_I_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem n7l_sAA4_H_I_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emax := hb0.2.2
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases h0emax with h8 | h8 | h8 | h8 | h8
                  · linarith only [h0, h6, h7, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                  · linarith only [h0, h3, h6, h7, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                  · linarith only [h0, h6, h7, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                  · linarith only [h1, h7, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                  · linarith only [h2, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                · linarith only [h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
              · linarith only [h6, hc34, hlam, hphi, ht12, ht23, u1ehi2]
            · linarith only [h3, h5, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · linarith only [h0, h4, hc34, hlam, hphi, ht12, ht23, u1ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h18 | h18
          · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
            · linarith only [h1, h18, h19, h3, hc12, hlam, hphi, u1ehi3]
            · linarith only [h19, hc23, hlam, hphi, ht12, u1ehi1]
          · linarith only [h0, h18, hc34, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h2, hc15, hlam, hphi, u1ehi0]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi2]
  · linarith only [h0, hc13, hlam, hphi, u1ehi0]

theorem n7l_sAA4_H_I_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h1, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
        · linarith only [h0, h1, h2, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
      · linarith only [h2, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
    · linarith only [h1, hc34, hlam, hphi, ht12, ht23, u1ehi2]
  · linarith only [h0, hc13, hlam, hphi, u1ehi0]

theorem n7l_sAA4_H_I_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4elo := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · rcases h1bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, h5, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h5, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        rcases p10_3 (m.d 0 1) (by simp) with h14 | h14
                        · rcases p10_3 (m.d 1 2) (by simp) with h15 | h15
                          · linarith only [h0, h15, hlam]
                          · linarith only [h15, h4, hlam]
                        · linarith only [h14, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        rcases p10_3 (m.d 0 1) (by simp) with h19 | h19
                        · rcases p10_3 (m.d 1 2) (by simp) with h20 | h20
                          · linarith only [h0, h20, hlam]
                          · linarith only [h20, h3, h5, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p10_1]
                        · linarith only [h19, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h5, h9, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h1, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h7, hc13, hlam, hphi, p10_1, u1ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hc14, hlam, hphi, p10_1, u1ehi0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h5, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, h5, h9, hc15, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h6, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h7, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                    · linarith only [h7, h9, hc34, hlam, hphi, u4elo1]
                  · linarith only [h7, h8, hc24, hlam, hphi, u4elo1]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                · linarith only [h47, h5, h6, hlam]
                · linarith only [h47, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h5, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
          · linarith only [h3, h4, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
          · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
            · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
              · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
                    · rcases h1bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h52, h56, hc01, hc45, hlam, hphi, ht0b, ht5b, p58_1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h3, h52, h56, hc01, hc45, hlam, hphi, ht0b, ht5b, p58_1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        rcases p58_3 (m.d 0 1) (by simp) with h62 | h62
                        · rcases p58_3 (m.d 1 2) (by simp) with h63 | h63
                          · linarith only [h0, h63, hlam]
                          · linarith only [h52, h63, hlam]
                        · linarith only [h62, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        rcases p58_3 (m.d 0 1) (by simp) with h67 | h67
                        · rcases p58_3 (m.d 1 2) (by simp) with h68 | h68
                          · linarith only [h0, h68, hlam]
                          · linarith only [h52, h56, h68, hc01, hc45, hlam, hphi, ht0b, ht5b, p58_1]
                        · linarith only [h67, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h0, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h3, hlam, p58_1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hc12, hlam, hphi, p58_1, u1ehi3]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h3, hc23, hlam, hphi, ht12, p58_1, u1ehi4]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h1, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h1, h52, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p58_1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p58_1, u1ehi3]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p58_1, u1ehi4]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hc14, hlam, hphi, p58_1, u1ehi0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h52, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h53, hlam, p58_1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h1, h3, h52, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p58_1, u1ehi4]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h2, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hc15, hlam, hphi, p58_1, u1ehi1]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h54, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [h55, hlam, p58_0]
                      · have p58_0 := h58c.1
                        have p58_1 := h58c.2.1
                        have p58_2 := h58c.2.2.1
                        have p58_3 := h58c.2.2.2
                        linarith only [hlam, p58_0]
                    · linarith only [h56, h57, hc34, hlam, hphi, u4elo2]
                  · linarith only [h55, h56, hc24, hlam, hphi, u4elo1]
                · linarith only [h55, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                · linarith only [h3, h52, h54, h95, hlam]
                · linarith only [h95, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h3, h52, h53, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo3]
          · linarith only [h52, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h102 | h102
    · linarith only [h0, h102, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h104 | h104
      · linarith only [h0, h104, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
        · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
          · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
            · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
              · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                · linarith only [h104, h110, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
                · linarith only [h110, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h102, h109, hc35, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h102, h108, hc34, hlam, hphi, ht12, ht23, u1ehi0]
          · linarith only [h106, h107, hc23, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h106, hc23, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAA4_H_I_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
                · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                        · linarith only [h16, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h16, h7, hlam]
                      · linarith only [h15, h5, hlam]
                    · linarith only [h14, h9, hlam, p0_1]
                  · linarith only [h13, hc14, hlam, hphi, p0_1, u1ehi1]
                · linarith only [h12, h7, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · rcases p0_3 (m.d 1 2) (by simp) with h26 | h26
      · linarith only [h26, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h28 | h28
        · linarith only [h28, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h30 | h30
          · linarith only [h30, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h32 | h32
            · linarith only [h32, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h34 | h34
              · rcases m.htr 0 1 3 (by decide) (by decide) with h35 | h35
                · rcases m.htr 0 1 4 (by decide) (by decide) with h36 | h36
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h37 | h37
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                      · linarith only [h26, h38, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                        · linarith only [h38, h40, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                            · linarith only [h43, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                            · linarith only [h30, h43, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                            · linarith only [h46, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                            · linarith only [h30, h46, hlam]
                    · linarith only [h37, hc15, hlam, hphi, p0_1, u1ehi2]
                  · linarith only [h36, hc14, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h35, hlam, p0_0]
              · linarith only [h34, hc12, hlam, hphi, p0_1, u1ehi2]
    · linarith only [h25, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h54 | h54
    · rcases p0_3 (m.d 1 2) (by simp) with h55 | h55
      · linarith only [h55, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h57 | h57
        · linarith only [h57, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h59 | h59
          · linarith only [h59, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h61 | h61
            · linarith only [h61, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h63 | h63
              · rcases m.htr 0 1 3 (by decide) (by decide) with h64 | h64
                · rcases m.htr 0 1 4 (by decide) (by decide) with h65 | h65
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h66 | h66
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
                        · linarith only [h55, h68, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                            · linarith only [h57, h71, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                              · linarith only [h73, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                              · linarith only [h61, h73, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                            · linarith only [h57, h76, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                              · linarith only [h78, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                              · linarith only [h61, h78, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                        · linarith only [h55, h81, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                            · linarith only [h57, h84, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                              · linarith only [h86, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                              · linarith only [h61, h86, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                            · linarith only [h57, h89, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                              · linarith only [h91, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                              · linarith only [h61, h91, hlam]
                    · linarith only [h66, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h65, hlam, p0_0]
                · linarith only [h64, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
              · linarith only [h63, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
    · linarith only [h54, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h99 | h99
    · rcases p0_3 (m.d 1 2) (by simp) with h100 | h100
      · linarith only [h100, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h102 | h102
        · linarith only [h102, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h104 | h104
          · linarith only [h104, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h106 | h106
            · linarith only [h106, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 1 3 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 1 4 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                        · linarith only [h100, h113, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                          · linarith only [h100, h115, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                            · linarith only [h104, h112, h113, h117, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                              · linarith only [h104, h119, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                                · linarith only [h112, h113, h117, h119, h121, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                                  · linarith only [h112, h113, h119, h121, h123, hc23, hc34, hlam, hphi]
                                  · linarith only [h112, h113, h123, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
                        · linarith only [h100, h126, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                          · linarith only [h100, h128, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                            · linarith only [h102, h130, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                              · linarith only [h104, h132, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                                · linarith only [h112, h130, h134, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h112, h134, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h111, hlam, p0_0]
                  · linarith only [h110, hc14, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h109, hc13, hlam, hphi, p0_1, u1ehi4]
              · linarith only [h108, hc12, hlam, hphi, p0_1, u1ehi4]
    · linarith only [h99, hlam, p0_0]
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

theorem n7l_sAA4_H_I_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h0, h6, hlam, ht01, u1elo2]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
      · linarith only [h0, h5, h9, hlam, ht01, u1elo1]
      · linarith only [h0, h9, hlam, ht01, u1elo2]
  · linarith only [h0, hlam, ht01, ht12, ht23, ht34, u4elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h13 | h13
    · rcases m.htr 0 1 3 (by decide) (by decide) with h14 | h14
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
        · linarith only [h0, h15, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h0, h15, hlam, ht01, ht12, ht23, ht34, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
        · linarith only [h0, h18, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h0, h18, hlam, ht01, ht12, ht23, ht34, u4elo4]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h21 | h21
      · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
        · linarith only [h0, h22, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h0, h22, hlam, ht01, ht12, ht23, ht34, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
        · linarith only [h0, h25, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h0, h25, hlam, ht01, ht12, ht23, ht34, u4elo4]

theorem n7l_sAA4_H_I_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
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
          · linarith only [h6, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h19 | h19
          · rcases p0_3 (m.d 1 5) (by simp) with h20 | h20
            · rcases m.htr 0 1 2 (by decide) (by decide) with h21 | h21
              · rcases m.htr 0 1 3 (by decide) (by decide) with h22 | h22
                · rcases m.htr 0 1 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h19, h23, hlam]
                  · linarith only [h23, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h22, h5, hlam, p0_1]
              · linarith only [h21, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h28 | h28
              · rcases m.htr 0 1 3 (by decide) (by decide) with h29 | h29
                · rcases m.htr 0 1 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h19, h30, hlam]
                  · linarith only [h30, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h29, h5, hlam, p0_1]
              · linarith only [h28, hlam, p0_0]
          · linarith only [h19, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · rcases p0_3 (m.d 1 2) (by simp) with h38 | h38
      · rcases p0_3 (m.d 1 3) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h41 | h41
          · rcases p0_3 (m.d 1 5) (by simp) with h42 | h42
            · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
              · linarith only [h38, h43, hlam]
              · linarith only [h43, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h46 | h46
              · linarith only [h38, h46, hlam]
              · linarith only [h46, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h41, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h50 | h50
        · linarith only [h50, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h52 | h52
          · rcases p0_3 (m.d 1 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · rcases m.htr 0 1 3 (by decide) (by decide) with h55 | h55
                · rcases m.htr 0 1 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h52, h56, hlam]
                  · linarith only [h38, h56, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h55, hlam, p0_0]
              · linarith only [h38, h54, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h61 | h61
              · rcases m.htr 0 1 3 (by decide) (by decide) with h62 | h62
                · rcases m.htr 0 1 4 (by decide) (by decide) with h63 | h63
                  · linarith only [h52, h63, hlam]
                  · linarith only [h38, h63, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h62, hlam, p0_0]
              · linarith only [h38, h61, hlam, p0_1]
          · linarith only [h52, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
    · linarith only [h37, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h71 | h71
    · rcases p0_3 (m.d 1 2) (by simp) with h72 | h72
      · rcases p0_3 (m.d 1 3) (by simp) with h73 | h73
        · rcases p0_3 (m.d 1 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 1 5) (by simp) with h75 | h75
            · linarith only [h75, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h77 | h77
              · linarith only [h72, h77, hlam]
              · linarith only [h77, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · linarith only [h73, h74, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h81 | h81
          · rcases p0_3 (m.d 1 5) (by simp) with h82 | h82
            · linarith only [h82, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h84 | h84
              · linarith only [h72, h84, hlam]
              · linarith only [h73, h84, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h81, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h88 | h88
        · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
          · rcases p0_3 (m.d 1 5) (by simp) with h90 | h90
            · linarith only [h90, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h92 | h92
              · rcases m.htr 0 1 3 (by decide) (by decide) with h93 | h93
                · linarith only [h88, h93, hlam]
                · linarith only [h72, h93, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h72, h92, hlam, p0_1]
          · linarith only [h89, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h98 | h98
          · rcases p0_3 (m.d 1 5) (by simp) with h99 | h99
            · linarith only [h99, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h101 | h101
              · rcases m.htr 0 1 3 (by decide) (by decide) with h102 | h102
                · rcases m.htr 0 1 4 (by decide) (by decide) with h103 | h103
                  · linarith only [h103, h98, hlam]
                  · linarith only [h103, h88, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h102, h72, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h101, h72, hlam, p0_1]
          · linarith only [h98, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
    · linarith only [h71, hlam, p0_0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h112 | h112
    · rcases p0_3 (m.d 1 2) (by simp) with h113 | h113
      · rcases p0_3 (m.d 1 3) (by simp) with h114 | h114
        · linarith only [h114, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 1 5) (by simp) with h117 | h117
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · linarith only [h118, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h112, h118, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · linarith only [h121, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h112, h121, hlam]
          · linarith only [h116, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1, u4ehi1]
      · linarith only [h113, hlam, p0_0]
    · linarith only [h112, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h128 | h128
    · rcases p0_3 (m.d 1 2) (by simp) with h129 | h129
      · rcases p0_3 (m.d 1 3) (by simp) with h130 | h130
        · rcases p0_3 (m.d 1 4) (by simp) with h131 | h131
          · rcases p0_3 (m.d 1 5) (by simp) with h132 | h132
            · linarith only [h132, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
              · linarith only [h134, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h128, h134, hlam]
          · linarith only [h131, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 1 5) (by simp) with h139 | h139
            · linarith only [h139, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · linarith only [h130, h141, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h128, h141, hlam]
          · linarith only [h138, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1, u4ehi1]
      · linarith only [h129, hlam, p0_0]
    · linarith only [h128, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h148 | h148
    · rcases p0_3 (m.d 1 2) (by simp) with h149 | h149
      · linarith only [h149, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h151 | h151
        · rcases p0_3 (m.d 1 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 1 5) (by simp) with h153 | h153
            · rcases m.htr 0 1 2 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 1 3 (by decide) (by decide) with h155 | h155
                · linarith only [h155, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h148, h155, hlam]
              · linarith only [h154, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h159 | h159
              · rcases m.htr 0 1 3 (by decide) (by decide) with h160 | h160
                · linarith only [h160, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h148, h160, hlam]
              · linarith only [h159, hc01, hlam, hphi, p0_1, u1elo2]
          · linarith only [h152, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2, u4ehi1]
        · linarith only [h151, hlam, p0_0]
    · linarith only [h148, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h169 | h169
    · rcases p0_3 (m.d 1 2) (by simp) with h170 | h170
      · rcases p0_3 (m.d 1 3) (by simp) with h171 | h171
        · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
          · rcases p0_3 (m.d 1 5) (by simp) with h173 | h173
            · linarith only [h173, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h175 | h175
              · linarith only [h170, h175, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h169, h175, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · linarith only [h172, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2, u4ehi1]
        · linarith only [h171, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h180 | h180
        · rcases p0_3 (m.d 1 4) (by simp) with h181 | h181
          · rcases p0_3 (m.d 1 5) (by simp) with h182 | h182
            · linarith only [h182, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h184 | h184
              · rcases m.htr 0 1 3 (by decide) (by decide) with h185 | h185
                · linarith only [h170, h185, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h169, h185, hlam]
              · linarith only [h170, h184, hc01, hlam, hphi, p0_1, u1elo2]
          · linarith only [h181, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2, u4ehi1]
        · linarith only [h180, hlam, p0_0]
    · linarith only [h169, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h193 | h193
    · rcases p0_3 (m.d 1 2) (by simp) with h194 | h194
      · linarith only [h194, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h196 | h196
        · rcases p0_3 (m.d 1 4) (by simp) with h197 | h197
          · rcases p0_3 (m.d 1 5) (by simp) with h198 | h198
            · rcases m.htr 0 1 2 (by decide) (by decide) with h199 | h199
              · rcases m.htr 0 1 3 (by decide) (by decide) with h200 | h200
                · linarith only [h196, h200, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h193, h200, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h193, h199, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h204 | h204
              · rcases m.htr 0 1 3 (by decide) (by decide) with h205 | h205
                · linarith only [h196, h205, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h193, h205, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h193, h204, hlam, p0_1]
          · linarith only [h197, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h210 | h210
          · rcases p0_3 (m.d 1 5) (by simp) with h211 | h211
            · rcases m.htr 0 1 2 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 1 3 (by decide) (by decide) with h213 | h213
                · rcases m.htr 0 1 4 (by decide) (by decide) with h214 | h214
                  · linarith only [h214, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h193, h214, hlam]
                · linarith only [h196, h213, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h193, h212, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h219 | h219
              · rcases m.htr 0 1 3 (by decide) (by decide) with h220 | h220
                · rcases m.htr 0 1 4 (by decide) (by decide) with h221 | h221
                  · linarith only [h221, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h193, h221, hlam]
                · linarith only [h196, h220, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h193, h219, hlam, p0_1]
          · linarith only [h210, hlam, p0_0]
    · linarith only [h193, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h228 | h228
    · rcases p0_3 (m.d 1 2) (by simp) with h229 | h229
      · rcases p0_3 (m.d 1 3) (by simp) with h230 | h230
        · linarith only [h230, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h232 | h232
          · rcases p0_3 (m.d 1 5) (by simp) with h233 | h233
            · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
              · linarith only [h229, h234, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h228, h234, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h237 | h237
              · linarith only [h229, h237, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h228, h237, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h232, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h241 | h241
        · linarith only [h241, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h243 | h243
          · rcases p0_3 (m.d 1 5) (by simp) with h244 | h244
            · rcases m.htr 0 1 2 (by decide) (by decide) with h245 | h245
              · rcases m.htr 0 1 3 (by decide) (by decide) with h246 | h246
                · rcases m.htr 0 1 4 (by decide) (by decide) with h247 | h247
                  · linarith only [h229, h247, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h228, h247, hlam]
                · linarith only [h246, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h228, h229, h245, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h252 | h252
              · rcases m.htr 0 1 3 (by decide) (by decide) with h253 | h253
                · rcases m.htr 0 1 4 (by decide) (by decide) with h254 | h254
                  · linarith only [h229, h254, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h228, h254, hlam]
                · linarith only [h253, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h228, h229, h252, hlam, p0_1]
          · linarith only [h243, hlam, p0_0]
    · linarith only [h228, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h262 | h262
    · rcases p0_3 (m.d 1 2) (by simp) with h263 | h263
      · rcases p0_3 (m.d 1 3) (by simp) with h264 | h264
        · rcases p0_3 (m.d 1 4) (by simp) with h265 | h265
          · rcases p0_3 (m.d 1 5) (by simp) with h266 | h266
            · linarith only [h266, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h268 | h268
              · linarith only [h263, h268, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h262, h268, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · linarith only [h265, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 1 5) (by simp) with h273 | h273
            · linarith only [h273, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h275 | h275
              · linarith only [h263, h264, h275, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h262, h264, h275, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h279 | h279
        · rcases p0_3 (m.d 1 4) (by simp) with h280 | h280
          · rcases p0_3 (m.d 1 5) (by simp) with h281 | h281
            · linarith only [h281, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h283 | h283
              · rcases m.htr 0 1 3 (by decide) (by decide) with h284 | h284
                · linarith only [h263, h279, h284, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h262, h263, h284, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h262, h263, h283, hlam, p0_1]
          · linarith only [h280, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h289 | h289
          · rcases p0_3 (m.d 1 5) (by simp) with h290 | h290
            · linarith only [h290, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h292 | h292
              · rcases m.htr 0 1 3 (by decide) (by decide) with h293 | h293
                · rcases m.htr 0 1 4 (by decide) (by decide) with h294 | h294
                  · linarith only [h263, h294, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h262, h294, hlam]
                · linarith only [h279, h293, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h262, h263, h292, hlam, p0_1]
          · linarith only [h289, hlam, p0_0]
    · linarith only [h262, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h302 | h302
    · rcases p0_3 (m.d 1 2) (by simp) with h303 | h303
      · linarith only [h303, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h305 | h305
        · rcases p0_3 (m.d 1 4) (by simp) with h306 | h306
          · rcases p0_3 (m.d 1 5) (by simp) with h307 | h307
            · rcases m.htr 0 1 2 (by decide) (by decide) with h308 | h308
              · rcases m.htr 0 1 3 (by decide) (by decide) with h309 | h309
                · linarith only [h305, h309, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h302, h309, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h302, h308, hlam, p0_1]
            · linarith only [h307, hlam, p0_0]
          · linarith only [h306, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo4, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h315 | h315
          · rcases p0_3 (m.d 1 5) (by simp) with h316 | h316
            · rcases m.htr 0 1 2 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 1 3 (by decide) (by decide) with h318 | h318
                · rcases m.htr 0 1 4 (by decide) (by decide) with h319 | h319
                  · linarith only [h315, h319, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h302, h319, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h302, h305, h318, hlam, p0_1]
              · linarith only [h302, h317, hlam, p0_1]
            · linarith only [h316, hlam, p0_0]
          · linarith only [h315, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo4, u4ehi1]
    · linarith only [h302, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h327 | h327
    · rcases p0_3 (m.d 1 2) (by simp) with h328 | h328
      · rcases p0_3 (m.d 1 3) (by simp) with h329 | h329
        · linarith only [h329, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h331 | h331
          · rcases p0_3 (m.d 1 5) (by simp) with h332 | h332
            · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
              · linarith only [h328, h333, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h327, h333, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h332, hlam, p0_0]
          · linarith only [h331, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo4, u4ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h338 | h338
        · linarith only [h338, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h340 | h340
          · rcases p0_3 (m.d 1 5) (by simp) with h341 | h341
            · rcases m.htr 0 1 2 (by decide) (by decide) with h342 | h342
              · rcases m.htr 0 1 3 (by decide) (by decide) with h343 | h343
                · rcases m.htr 0 1 4 (by decide) (by decide) with h344 | h344
                  · linarith only [h328, h340, h344, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h327, h328, h344, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h327, h343, hlam, p0_1]
              · linarith only [h327, h328, h342, hlam, p0_1]
            · linarith only [h341, hlam, p0_0]
          · linarith only [h340, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo4, u4ehi1]
    · linarith only [h327, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo4, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_H_I_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi8, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo3]

theorem n7l_sAA4_H_I_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA4_H_I_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi8, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo3]

theorem n7l_sAA4_H_L_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_H_L_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_H_L_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · linarith only [h0, h1, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h0, h1, h3, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h10, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h0, h1, h10, h3, h9, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13 | h13
                · linarith only [h13, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h0, h1, h13, h6, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h16 | h16
            · linarith only [h16, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h18 | h18
              · linarith only [h18, h3, h6, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h20 | h20
                · linarith only [h20, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h1, h20, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h1, h20, h22, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h25 | h25
        · linarith only [h0, h25, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h27 | h27
          · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
            · linarith only [h28, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
              · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
                · linarith only [h31, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h0, h1, h27, h31, hlam]
              · linarith only [h27, h3, h30, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h35 | h35
            · linarith only [h35, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h37 | h37
              · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
                · linarith only [h38, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h35, h37, h38, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                · linarith only [h41, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                  · linarith only [h0, h1, h3, h41, h43, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                    · linarith only [h0, h25, h45, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                      · linarith only [h0, h27, h47, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                        · linarith only [h0, h1, h41, h45, h49, hc12, hc24, hlam, hphi]
                        · linarith only [h0, h1, h49, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h52 | h52
    · linarith only [h52, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h54 | h54
      · rcases m.htr 0 2 4 (by decide) (by decide) with h55 | h55
        · linarith only [h55, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h57 | h57
          · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
            · linarith only [h58, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h60 | h60
              · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
                · linarith only [h61, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h54, h55, h60, h61, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h64 | h64
                · linarith only [h64, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h55, h57, h64, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h67 | h67
            · linarith only [h67, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
              · linarith only [h54, h57, h69, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                · linarith only [h71, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                          · linarith only [h54, h55, h67, h71, h74, h76, h77, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                            · linarith only [h54, h69, h71, h79, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                              · linarith only [h54, h55, h71, h77, h81, hc23, hc34, hlam, hphi]
                              · linarith only [h54, h55, h74, h76, h81, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h54, h55, h74, h76, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h54, h55, h74, h75, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                      · linarith only [h54, h57, h74, h86, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h88 | h88
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                          · linarith only [h54, h89, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                          · linarith only [h54, h55, h71, h74, h88, h89, hc23, hc34, hlam, hphi]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                          · linarith only [h54, h92, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                            · linarith only [h54, h55, h71, h94, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                              · linarith only [h0, h74, h88, h92, h96, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h54, h55, h96, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h54, h73, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h100 | h100
        · linarith only [h100, h54, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h102 | h102
          · rcases m.htr 0 3 4 (by decide) (by decide) with h103 | h103
            · linarith only [h103, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h105 | h105
              · rcases m.htr 0 4 5 (by decide) (by decide) with h106 | h106
                · linarith only [h106, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h102, h103, h106, h54, hlam]
              · linarith only [h102, h105, h54, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
            · linarith only [h110, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
                · linarith only [h113, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h110, h112, h113, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h116 | h116
                · linarith only [h116, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                          · linarith only [h0, h110, h118, h122, h54, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
                            · linarith only [h0, h112, h122, h124, h54, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                              · linarith only [h116, h119, h126, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                              · linarith only [h0, h100, h119, h121, h126, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h129 | h129
                          · linarith only [h0, h110, h118, h129, h54, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                            · linarith only [h0, h112, h119, h121, h129, h131, h54, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                              · linarith only [h119, h121, h133, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                                · linarith only [h121, h135, h52, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h0, h129, h135, h54, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h118, h120, h54, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h118, h119, h54, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                    · linarith only [h0, h100, h118, h140, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                      · linarith only [h0, h102, h118, h142, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                                · linarith only [h116, h145, h148, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                                · linarith only [h0, h110, h144, h148, h54, hc01, hc14, hlam, hphi]
                              · linarith only [h140, h144, h147, hlam]
                            · linarith only [h116, h140, h144, h145, h146, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h118, h145, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                              · linarith only [h144, h154, h156, h52, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h140, h156, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h118, h155, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h118, h154, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sAA4_H_L_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h2, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h2, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h1, hc01, hlam, hphi, u1elo3]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA4_H_L_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h1, h7, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h4, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
                  · linarith only [h1, h12, h14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h14, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h17 | h17
              · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h18, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h1, h18, h20, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h20, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h23, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h1, h23, h25, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h25, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
            · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h30, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                  · linarith only [h1, h30, h32, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                    · linarith only [h1, h34, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h28, h34, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                · linarith only [h0, h37, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                  · linarith only [h0, h39, h4, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                    · linarith only [h1, h41, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h28, h37, h41, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h44 | h44
              · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                · linarith only [h0, h45, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                  · linarith only [h0, h4, h47, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                    · linarith only [h1, h28, h49, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                      · linarith only [h2, h51, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h44, h45, h49, h51, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                · linarith only [h0, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h0, h4, h56, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                    · linarith only [h1, h28, h58, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                      · linarith only [h2, h44, h60, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                            · linarith only [h2, h44, h54, h58, h62, h64, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h28, h54, h63, h64, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                            · linarith only [h0, h4, h63, h67, hc12, hc34, hlam, hphi, ht23]
                            · rcases h4bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h54, h58, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u0elo3]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h4, hlam, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h28, hlam, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h44, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h2, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h56, hlam, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h58, hlam, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h60, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h63, hc04, hc45, hlam, hphi, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h54, h58, h63, hc12, hc45, hlam, hphi, ht23, ht34, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h63, hc34, hc45, hlam, hphi, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h63, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h2, h54, h58, h62, hc12, hc23, hlam, hphi, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h54, h58, h62, hc12, hc23, hlam, hphi, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h62, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h67, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                rcases p69_3 (m.d 0 4) (by simp) with h90 | h90
                                · linarith only [h90, hlam, p69_0]
                                · rcases p69_3 (m.d 1 4) (by simp) with h92 | h92
                                  · linarith only [h60, h92, hlam]
                                  · rcases p69_3 (m.d 2 4) (by simp) with h94 | h94
                                    · linarith only [h63, h94, hlam]
                                    · linarith only [h4, h94, hlam]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                rcases p69_3 (m.d 0 4) (by simp) with h97 | h97
                                · linarith only [h44, h97, hlam]
                                · linarith only [h2, h97, hlam]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h1, h28, h54, hc12, hc45, hlam, hphi, ht23, ht34, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h104 | h104
                            · rcases h4bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [hlam, p105_0]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h54, h58, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u0elo3]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h4, hlam, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h28, hlam, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h44, hlam, p105_0]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h2, hlam, p105_0]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [hlam, p105_0]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h56, hlam, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h58, hlam, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h60, hlam, p105_0]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                rcases p105_3 (m.d 0 4) (by simp) with h116 | h116
                                · linarith only [h116, h4, hlam]
                                · rcases p105_3 (m.d 1 4) (by simp) with h118 | h118
                                  · linarith only [h118, h56, hlam]
                                  · rcases p105_3 (m.d 2 4) (by simp) with h120 | h120
                                    · rcases p105_3 (m.d 3 4) (by simp) with h121 | h121
                                      · rcases p105_3 (m.d 4 5) (by simp) with h122 | h122
                                        · linarith only [h103, h122, hlam]
                                        · linarith only [h122, h44, hlam]
                                      · linarith only [h121, h28, hlam]
                                    · linarith only [h120, h4, hlam]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                rcases p105_3 (m.d 0 4) (by simp) with h127 | h127
                                · linarith only [h127, h4, hlam]
                                · linarith only [h127, h2, hlam]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [hlam, p105_0]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h62, hlam, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h2, h44, h54, h58, h62, hc12, hc34, hlam, hphi, ht23, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                rcases p105_3 (m.d 0 4) (by simp) with h133 | h133
                                · linarith only [h133, h28, hlam]
                                · rcases p105_3 (m.d 1 4) (by simp) with h135 | h135
                                  · linarith only [h135, h58, hlam]
                                  · rcases p105_3 (m.d 2 4) (by simp) with h137 | h137
                                    · linarith only [h137, h62, hlam]
                                    · linarith only [h137, h4, hlam]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                rcases p105_3 (m.d 0 4) (by simp) with h140 | h140
                                · linarith only [h140, h28, hlam]
                                · linarith only [h140, h2, hlam]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [hlam, p105_0]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h2, h44, h54, h58, hc12, hc34, hlam, hphi, ht23, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h103, h2, h54, h58, hc12, hc24, hlam, hphi, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h103, h54, h58, hc12, hc24, hlam, hphi, p105_1]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h103, hlam, p105_0]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [h104, hlam, p105_0]
                              · have p105_0 := h105c.1
                                have p105_1 := h105c.2.1
                                have p105_2 := h105c.2.2.1
                                have p105_3 := h105c.2.2.2
                                linarith only [hlam, p105_0]
                            · linarith only [h103, h104, h62, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h152 | h152
                            · linarith only [h0, h103, h152, h4, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h152, h54, h62, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h3, hc01, hlam, hphi, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA4_H_L_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo3]

theorem n7l_sAA4_H_L_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi0]

theorem n7l_sAA4_H_L_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi0]

theorem n7l_sAA4_H_L_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi0]

theorem n7l_sAA4_H_L_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
    · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]

theorem n7l_sAA4_H_L_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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

theorem n7l_sAA4_H_L_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
      · linarith only [h4, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
        · linarith only [h6, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
          · linarith only [h0, h4, h6, h8, hc24, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
            · linarith only [h0, h10, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h0, h10, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]

theorem n7l_sAA4_H_L_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h39 | h39
    · linarith only [h39, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h39, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h42 | h42
    · linarith only [h42, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h42, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_H_L_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_H_L_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h4, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · linarith only [h0, h1, h3, h4, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
        · linarith only [h7, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h1, h7, h9, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
            · linarith only [h0, h1, h11, h3, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
              · linarith only [h1, h13, h7, hc01, hlam, hphi, u1elo3]
              · linarith only [h0, h1, h13, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h16 | h16
    · linarith only [h16, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h18 | h18
      · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
        · linarith only [h19, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
          · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
              · linarith only [h16, h19, h21, h23, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                · linarith only [h21, h23, h25, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h18, h25, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · linarith only [h18, h22, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
            · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
              · linarith only [h19, h30, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
              · linarith only [h21, h29, h30, hlam]
            · linarith only [h0, h18, h29, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
        · linarith only [h34, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
          · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
            · linarith only [h0, h18, h37, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
              · linarith only [h34, h36, h37, h39, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                · linarith only [h16, h39, h41, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h36, h37, h41, hc45, hlam, hphi, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
            · linarith only [h0, h18, h44, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
              · linarith only [h34, h46, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
                · linarith only [h0, h36, h46, h48, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h36, h48, hc01, hc45, hlam, hphi, ht12, ht23, ht34]

theorem n7l_sAA4_H_L_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi6]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA4_H_L_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi8]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo3]

theorem n7l_sAA4_H_L_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi6]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA4_H_R_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.1
  have h4elo := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sAA4_H_R_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h6, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h10, h11, h6, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h10, h14, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases h1bigk with h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p16_1, u4ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p16_1, u4ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h8, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p16_1, u4ehi3]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p16_1, u4ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h10, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p16_1, u4ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h1, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h6, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h7, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p16_1, u4ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h10, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p16_1, u4ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h2, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h7, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h8, hlam, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, hlam, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h3, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h9, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h6, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p16_1, u4ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h42, h8, h9, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h42, h44, h8, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h44, h8, h9, hc45, hlam, hphi, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                        · linarith only [h0, h4, h47, h49, h5, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h47, h48, h49, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h47, h48, h8, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                        · rcases h1bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            rcases p55_3 (m.d 0 1) (by simp) with h58 | h58
                            · rcases p55_3 (m.d 1 2) (by simp) with h59 | h59
                              · linarith only [h0, h59, hlam]
                              · linarith only [h59, h6, hlam]
                            · linarith only [h58, hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h53, hc01, hlam, hphi, ht0b, ht45, ht5b, p55_1, u4ehi4]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h53, hc01, hlam, hphi, ht0b, ht45, ht5b, p55_1, u4ehi4]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h0, hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h0, h53, hc01, hlam, hphi, ht0b, ht45, ht5b, p55_1, u4ehi4]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h0, h53, hc01, hlam, hphi, ht0b, ht45, ht5b, p55_1, u4ehi4]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h1, hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h6, hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h8, hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h47, hlam, p55_1]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h2, hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h7, hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h0, h4, h5, h53, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p55_1, u4ehi4]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h3, hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p55_1]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [h53, hlam, p55_0]
                          · have p55_0 := h55c.1
                            have p55_1 := h55c.2.1
                            have p55_2 := h55c.2.2.1
                            have p55_3 := h55c.2.2.2
                            linarith only [hlam, p55_0]
                        · linarith only [h53, h54, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h86 | h86
                        · linarith only [h0, h4, h5, h53, h86, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases h1bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            rcases p88_3 (m.d 0 1) (by simp) with h91 | h91
                            · rcases p88_3 (m.d 1 2) (by simp) with h92 | h92
                              · linarith only [h0, h92, hlam]
                              · linarith only [h6, h92, hlam]
                            · linarith only [h91, hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h53, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h0, hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h0, h53, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h1, hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h6, hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h8, hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h47, hlam, p88_1]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h2, hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h7, hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h53, hlam, p88_1]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h3, hlam, p88_0]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p88_1]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi1]
                          · have p88_0 := h88c.1
                            have p88_1 := h88c.2.1
                            have p88_2 := h88c.2.2.1
                            have p88_3 := h88c.2.2.2
                            linarith only [hlam, p88_0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                  · linarith only [h118, h6, h7, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h120 | h120
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                        · linarith only [h0, h118, h120, h122, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h118, h120, h121, h122, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h120, h121, h6, h7, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                        · rcases h1bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            rcases p128_3 (m.d 0 1) (by simp) with h131 | h131
                            · rcases p128_3 (m.d 1 2) (by simp) with h132 | h132
                              · linarith only [h0, h132, hlam]
                              · linarith only [h132, h6, hlam]
                            · linarith only [h131, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h126, hc01, hlam, hphi, ht0b, ht45, ht5b, p128_1, u4ehi4]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h126, hc01, hlam, hphi, ht0b, ht45, ht5b, p128_1, u4ehi4]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h0, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h7, hlam, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h126, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p128_1, u4ehi4]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h1, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h6, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h118, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h120, hlam, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h2, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h0, h118, h4, h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h0, h118, h126, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p128_1, u4ehi4]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h3, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h6, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h126, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [hlam, p128_0]
                        · linarith only [h118, h126, h127, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h159 | h159
                        · linarith only [h0, h126, h159, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases h1bigk with h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            rcases p161_3 (m.d 0 1) (by simp) with h164 | h164
                            · rcases p161_3 (m.d 1 2) (by simp) with h165 | h165
                              · linarith only [h0, h165, hlam]
                              · linarith only [h165, h6, hlam]
                            · linarith only [h164, hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h126, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h0, hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h7, hlam, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h118, h159, h7, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h1, hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h6, hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h118, hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h120, hlam, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h2, hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h118, h159, hc12, hc45, hlam, hphi, ht23, ht34, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h118, h159, h6, hc23, hc45, hlam, hphi, ht34, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h126, hlam, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h3, hlam, p161_0]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h6, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [h3, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p161_1]
                          · have p161_0 := h161c.1
                            have p161_1 := h161c.2.1
                            have p161_2 := h161c.2.2.1
                            have p161_3 := h161c.2.2.2
                            linarith only [hlam, p161_0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
                · linarith only [h0, h191, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
                        · linarith only [h1, h193, h196, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h195, h196, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h199 | h199
                        · linarith only [h0, h195, h199, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases h1bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            rcases p201_3 (m.d 0 1) (by simp) with h203 | h203
                            · rcases p201_3 (m.d 1 2) (by simp) with h204 | h204
                              · linarith only [h204, hlam, p201_0]
                              · rcases p201_3 (m.d 1 3) (by simp) with h206 | h206
                                · linarith only [h1, h206, hlam]
                                · linarith only [h206, h6, hlam]
                            · linarith only [h203, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h194, hc01, hc35, hlam, hphi, ht0b, ht5b, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h193, hc01, hlam, hphi, ht0b, ht45, ht5b, p201_1, u4ehi3]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h193, h195, hc01, hlam, hphi, ht0b, ht45, ht5b, p201_1, u4ehi3]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h0, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h6, hlam, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h191, hlam, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h193, h195, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p201_1, u4ehi3]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h1, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h0, h193, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p201_1, u4ehi3]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h0, h193, h195, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p201_1, u4ehi3]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h2, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h195, hc12, hc45, hlam, hphi, ht23, ht34, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h193, hlam, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h195, hlam, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h3, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [h194, hlam, p201_0]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p201_1, u4ehi1]
                          · have p201_0 := h201c.1
                            have p201_1 := h201c.2.1
                            have p201_2 := h201c.2.2.1
                            have p201_3 := h201c.2.2.2
                            linarith only [hlam, p201_0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
                      · linarith only [h193, h194, h233, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                        · linarith only [h193, h233, h235, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h193, h194, h235, hc45, hlam, hphi, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h240 | h240
                        · linarith only [h0, h193, h238, h240, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h193, h238, h239, h240, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h193, h238, h239, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
                        · rcases h1bigk with h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            rcases p246_3 (m.d 0 1) (by simp) with h248 | h248
                            · rcases p246_3 (m.d 1 2) (by simp) with h249 | h249
                              · linarith only [h249, hlam, p246_0]
                              · rcases p246_3 (m.d 1 3) (by simp) with h251 | h251
                                · linarith only [h1, h251, hlam]
                                · linarith only [h251, h6, hlam]
                            · linarith only [h248, hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            rcases p246_3 (m.d 0 1) (by simp) with h255 | h255
                            · rcases p246_3 (m.d 1 2) (by simp) with h256 | h256
                              · linarith only [h0, h256, hlam]
                              · rcases p246_3 (m.d 1 3) (by simp) with h258 | h258
                                · linarith only [h258, hlam, p246_0]
                                · rcases p246_3 (m.d 1 4) (by simp) with h260 | h260
                                  · linarith only [h2, h260, hlam]
                                  · linarith only [h193, h260, hlam]
                            · linarith only [h255, hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h244, hc01, hlam, hphi, ht0b, ht45, ht5b, p246_1, u4ehi4]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h244, hc01, hlam, hphi, ht0b, ht45, ht5b, p246_1, u4ehi4]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h0, hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h6, hlam, p246_1]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h191, hlam, p246_1]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h244, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p246_1, u4ehi4]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h1, hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h193, hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h238, hlam, p246_1]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h2, hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h0, h193, h4, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h0, h193, h244, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p246_1, u4ehi4]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h3, hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h0, h238, h245, h4, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [h244, hlam, p246_0]
                          · have p246_0 := h246c.1
                            have p246_1 := h246c.2.1
                            have p246_2 := h246c.2.2.1
                            have p246_3 := h246c.2.2.2
                            linarith only [hlam, p246_0]
                        · linarith only [h193, h244, h245, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h287 | h287
                        · linarith only [h0, h244, h287, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases h1bigk with h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            rcases p289_3 (m.d 0 1) (by simp) with h291 | h291
                            · rcases p289_3 (m.d 1 2) (by simp) with h292 | h292
                              · linarith only [h292, hlam, p289_0]
                              · rcases p289_3 (m.d 1 3) (by simp) with h294 | h294
                                · linarith only [h1, h294, hlam]
                                · linarith only [h294, h6, hlam]
                            · linarith only [h291, hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            rcases p289_3 (m.d 0 1) (by simp) with h298 | h298
                            · rcases p289_3 (m.d 1 2) (by simp) with h299 | h299
                              · linarith only [h0, h299, hlam]
                              · rcases p289_3 (m.d 1 3) (by simp) with h301 | h301
                                · linarith only [h301, hlam, p289_0]
                                · rcases p289_3 (m.d 1 4) (by simp) with h303 | h303
                                  · linarith only [h2, h303, hlam]
                                  · linarith only [h193, h303, hlam]
                            · linarith only [h298, hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p289_1, u4ehi1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h244, hc01, hlam, hphi, ht0b, ht45, ht5b, p289_1, u4ehi1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h0, hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h6, hlam, p289_1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h191, hlam, p289_1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h244, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p289_1, u4ehi1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h1, hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p289_1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h193, hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h238, hlam, p289_1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h2, hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p289_1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h193, h287, hc13, hc45, hlam, hphi, ht34, p289_1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h244, hlam, p289_1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h3, hlam, p289_0]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p289_1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p289_1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p289_1, u4ehi1]
                          · have p289_0 := h289c.1
                            have p289_1 := h289c.2.1
                            have p289_2 := h289c.2.2.1
                            have p289_3 := h289c.2.2.2
                            linarith only [hlam, p289_0]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc15, hlam, hphi, ht01, u0ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, ht01, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sAA4_H_R_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_H_R_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_H_R_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_H_R_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.1
  have h4elo := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sAA4_H_R_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h4bigk := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h10, h11, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h10, h14, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h4bigk with h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h1, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi4]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            rcases p16_3 (m.d 0 4) (by simp) with h19 | h19
                            · rcases p16_3 (m.d 1 4) (by simp) with h20 | h20
                              · linarith only [h1, h20, hlam]
                              · linarith only [h20, h5, hlam]
                            · linarith only [h19, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            rcases p16_3 (m.d 0 4) (by simp) with h24 | h24
                            · rcases p16_3 (m.d 1 4) (by simp) with h25 | h25
                              · linarith only [h1, h25, hlam]
                              · linarith only [h25, h7, hlam]
                            · linarith only [h24, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            rcases p16_3 (m.d 0 4) (by simp) with h29 | h29
                            · rcases p16_3 (m.d 1 4) (by simp) with h30 | h30
                              · linarith only [h1, h30, hlam]
                              · linarith only [h30, h8, hlam]
                            · linarith only [h29, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h1, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            rcases p16_3 (m.d 0 4) (by simp) with h36 | h36
                            · rcases p16_3 (m.d 1 4) (by simp) with h37 | h37
                              · rcases p16_3 (m.d 2 4) (by simp) with h38 | h38
                                · linarith only [h38, h5, hlam]
                                · rcases p16_3 (m.d 3 4) (by simp) with h40 | h40
                                  · linarith only [h40, h7, hlam]
                                  · rcases p16_3 (m.d 4 5) (by simp) with h42 | h42
                                    · linarith only [h42, h8, hlam]
                                    · linarith only [h10, h42, hlam]
                              · linarith only [h37, h5, hlam]
                            · linarith only [h10, h36, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            rcases p16_3 (m.d 0 4) (by simp) with h47 | h47
                            · rcases p16_3 (m.d 1 4) (by simp) with h48 | h48
                              · rcases p16_3 (m.d 2 4) (by simp) with h49 | h49
                                · linarith only [h49, h5, hlam]
                                · linarith only [h49, h9, hlam]
                              · linarith only [h48, h7, hlam]
                            · linarith only [h0, h3, h4, h47, h7, hc01, hlam, hphi, u0ehi4]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h10, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h3, h4, h7, h8, hc01, hc24, hlam, hphi, ht12, p16_1, u0ehi4, u1ehi4]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h5, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h10, h4, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h4, h7, h8, hc01, hc34, hlam, hphi, ht12, ht23, p16_1, u0ehi3, u1ehi4]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h7, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h9, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h14, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h3, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h8, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h4, h7, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h4, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                        · rcases h4bigk with h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p72_1, u1ehi4]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            rcases p72_3 (m.d 0 4) (by simp) with h75 | h75
                            · rcases p72_3 (m.d 1 4) (by simp) with h76 | h76
                              · linarith only [h1, h76, hlam]
                              · linarith only [h5, h76, hlam]
                            · linarith only [h75, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            rcases p72_3 (m.d 0 4) (by simp) with h80 | h80
                            · rcases p72_3 (m.d 1 4) (by simp) with h81 | h81
                              · linarith only [h1, h81, hlam]
                              · linarith only [h7, h81, hlam]
                            · linarith only [h80, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            rcases p72_3 (m.d 0 4) (by simp) with h85 | h85
                            · rcases p72_3 (m.d 1 4) (by simp) with h86 | h86
                              · linarith only [h1, h86, hlam]
                              · linarith only [h8, h86, hlam]
                            · linarith only [h85, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h1, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h0, h4, h7, h70, hc01, hc45, hlam, hphi, ht0b, ht5b, p72_1]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h0, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            rcases p72_3 (m.d 0 4) (by simp) with h94 | h94
                            · rcases p72_3 (m.d 1 4) (by simp) with h95 | h95
                              · rcases p72_3 (m.d 2 4) (by simp) with h96 | h96
                                · linarith only [h5, h96, hlam]
                                · linarith only [h70, h96, hlam]
                              · linarith only [h95, hlam, p72_0]
                            · linarith only [h3, h94, hlam]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h0, h3, h4, h7, h8, hc01, hc24, hlam, hphi, ht12, p72_1, u0ehi4, u1ehi4]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h5, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h9, hlam, p72_1]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h0, h4, h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p72_1]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h0, h3, h4, h7, hc01, hlam, hphi, p72_1, u0ehi4]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h7, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p72_1]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p72_1]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h3, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h8, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h70, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [h71, hlam, p72_0]
                          · have p72_0 := h72c.1
                            have p72_1 := h72c.2.1
                            have p72_2 := h72c.2.2.1
                            have p72_3 := h72c.2.2.2
                            linarith only [hlam, p72_0]
                        · linarith only [h0, h5, h70, h71, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
                        · linarith only [h0, h117, h4, h7, h70, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h117, h4, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h3, h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                · linarith only [h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
              · linarith only [h6, hc25, hlam, hphi, ht12, u1ehi1]
            · linarith only [h4, h5, hc24, hlam, hphi, ht12, u1ehi2]
          · linarith only [h4, hc23, hlam, hphi, ht12, u1ehi1]
        · linarith only [h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA4_H_R_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h1, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
          · linarith only [h0, h1, h3, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
        · linarith only [h3, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
      · linarith only [h2, hc35, hlam, hphi, ht12, ht23, u1ehi2]
    · linarith only [h1, hc34, hlam, hphi, ht12, ht23, u1ehi2]
  · linarith only [h0, hc13, hlam, hphi, u1ehi0]

theorem n7l_sAA4_H_R_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.1
  have h4elo := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sAA4_H_R_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h13, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h10, h13, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h16, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                          · linarith only [h10, h18, h8, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h10, h20, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                            · rcases h1bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi2]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                rcases p22_3 (m.d 0 1) (by simp) with h25 | h25
                                · rcases p22_3 (m.d 1 2) (by simp) with h26 | h26
                                  · linarith only [h0, h26, hlam]
                                  · linarith only [h26, h7, hlam]
                                · linarith only [h25, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                rcases p22_3 (m.d 0 1) (by simp) with h30 | h30
                                · rcases p22_3 (m.d 1 2) (by simp) with h31 | h31
                                  · linarith only [h0, h31, hlam]
                                  · linarith only [h31, h8, hlam]
                                · linarith only [h30, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                rcases p22_3 (m.d 0 1) (by simp) with h35 | h35
                                · rcases p22_3 (m.d 1 2) (by simp) with h36 | h36
                                  · linarith only [h0, h36, hlam]
                                  · linarith only [h36, h9, hlam]
                                · linarith only [h35, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hc12, hlam, hphi, p22_1, u1ehi2]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p22_1, u1ehi4]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h1, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h7, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hc13, hlam, hphi, p22_1, u1ehi3]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, h10, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p22_1, u1ehi3]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h2, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h8, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hc14, hlam, hphi, p22_1, u1ehi2]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h10, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h3, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h9, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, h10, h5, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p22_1, u1ehi2]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, h10, h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                      · linarith only [h60, h8, h9, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                        · linarith only [h0, h62, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                          · linarith only [h60, h64, h8, h9, hc25, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h0, h5, h6, h64, h8, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h67 | h67
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                        · linarith only [h0, h5, h69, h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                          · linarith only [h0, h5, h67, h71, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h68, h7, h71, h8, hc14, hlam, hphi, u1ehi2]
                      · linarith only [h67, h68, h8, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                        · linarith only [h0, h5, h7, h76, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                            · rcases h1bigk with h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                rcases p80_3 (m.d 0 1) (by simp) with h82 | h82
                                · rcases p80_3 (m.d 1 2) (by simp) with h83 | h83
                                  · linarith only [h83, hlam, p80_0]
                                  · rcases p80_3 (m.d 1 3) (by simp) with h85 | h85
                                    · linarith only [h1, h85, hlam]
                                    · rcases p80_3 (m.d 1 4) (by simp) with h87 | h87
                                      · linarith only [h2, h87, hlam]
                                      · linarith only [h8, h87, hlam]
                                · linarith only [h82, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                rcases p80_3 (m.d 0 1) (by simp) with h91 | h91
                                · rcases p80_3 (m.d 1 2) (by simp) with h92 | h92
                                  · linarith only [h0, h92, hlam]
                                  · linarith only [h7, h92, hlam]
                                · linarith only [h91, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h75, hc01, hlam, hphi, ht0b, ht45, ht5b, p80_1, u4ehi4]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                rcases p80_3 (m.d 0 1) (by simp) with h97 | h97
                                · rcases p80_3 (m.d 1 2) (by simp) with h98 | h98
                                  · linarith only [h0, h98, hlam]
                                  · rcases p80_3 (m.d 1 3) (by simp) with h100 | h100
                                    · linarith only [h1, h100, hlam]
                                    · rcases p80_3 (m.d 1 4) (by simp) with h102 | h102
                                      · linarith only [h102, h2, hlam]
                                      · linarith only [h102, h75, hlam]
                                · linarith only [h97, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h5, h67, h78, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p80_1, u1ehi2]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h8, hlam, p80_1]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h67, hlam, p80_1]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h1, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h7, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h75, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p80_1, u4ehi4]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h67, h7, hlam, p80_1]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h2, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h7, hc14, hlam, hphi, p80_1, u1ehi2]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p80_1, u1ehi2]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h5, h67, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p80_1]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h3, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hc15, hlam, hphi, p80_1, u1ehi1]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h0, h5, h67, h78, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p80_1, u1ehi2]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [h75, hlam, p80_0]
                              · have p80_0 := h80c.1
                                have p80_1 := h80c.2.1
                                have p80_2 := h80c.2.2.1
                                have p80_3 := h80c.2.2.2
                                linarith only [hlam, p80_0]
                            · linarith only [h0, h5, h6, h7, h76, h79, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                          · linarith only [h75, h78, h8, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                        · linarith only [h128, h7, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                          · linarith only [h0, h130, h5, h7, h75, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                          · linarith only [h130, h7, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                  · linarith only [h0, h133, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h135 | h135
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
                          · linarith only [h0, h133, h135, h137, h138, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h133, h135, h136, h138, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h135, h137, h7, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                      · linarith only [h133, h135, h136, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h145 | h145
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
                            · linarith only [h0, h144, h146, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h143, h146, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h133, h143, h145, hlam]
                        · linarith only [h144, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h152 | h152
                          · linarith only [h133, h143, h151, h152, hc23, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h0, h133, h152, h5, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · linarith only [h151, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
            · linarith only [h5, hc24, hlam, hphi, ht01, ht12, u0ehi1]
          · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc15, hlam, hphi, ht01, u0ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, ht01, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sAA4_H_R_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_H_R_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_H_R_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_H_R_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_H_R_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_H_R_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_M_IR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
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
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_IR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
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
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_IR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_M_IR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_M_IR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA4_M_IR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem n7l_sAA4_M_IR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1ehi := hb1.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
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
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
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
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_IR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h2, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
            · linarith only [h0, h2, h3, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · linarith only [h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
        · linarith only [h3, hc34, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht12, u1ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA4_M_IR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4elo := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h3, h8, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2, h7, h9, hc34, hlam, hphi, u4elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                    · rcases h1bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13_1]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13_1]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        rcases p13_3 (m.d 0 1) (by simp) with h17 | h17
                        · rcases p13_3 (m.d 1 2) (by simp) with h18 | h18
                          · linarith only [h0, h18, hlam]
                          · linarith only [h18, h4, hlam]
                        · linarith only [h17, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        rcases p13_3 (m.d 0 1) (by simp) with h22 | h22
                        · rcases p13_3 (m.d 1 2) (by simp) with h23 | h23
                          · linarith only [h0, h23, hlam]
                          · linarith only [h23, h5, hlam]
                        · linarith only [h22, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h6, h8, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13_1]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h1, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h3, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h7, hc13, hlam, hphi, p13_1, u1ehi4]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h2, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h4, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h6, hlam, p13_1]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hc14, hlam, hphi, p13_1, u1ehi4]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hc15, hlam, hphi, p13_1, u1ehi0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h5, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h2, h6, h7, h8, hc23, hlam, hphi, ht34, p13_1, u4elo0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h7, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                    · linarith only [h12, h8, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h6, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
              · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                · linarith only [h3, h5, h50, h51, hlam]
                · linarith only [h51, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h50, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
          · linarith only [h3, h4, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
          · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
            · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
              · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h61 | h61
                    · rcases h1bigk with h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h56, h60, h61, hc01, hc45, hlam, hphi, ht0b, ht5b, p62_1]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h3, h56, h60, h61, hc01, hc45, hlam, hphi, ht0b, ht5b, p62_1]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        rcases p62_3 (m.d 0 1) (by simp) with h66 | h66
                        · rcases p62_3 (m.d 1 2) (by simp) with h67 | h67
                          · linarith only [h0, h67, hlam]
                          · linarith only [h56, h67, hlam]
                        · linarith only [h66, hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        rcases p62_3 (m.d 0 1) (by simp) with h71 | h71
                        · rcases p62_3 (m.d 1 2) (by simp) with h72 | h72
                          · linarith only [h0, h72, hlam]
                          · linarith only [h57, h72, hlam]
                        · linarith only [h71, hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h0, hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h3, hlam, p62_1]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h59, hc12, hlam, hphi, p62_1, u1ehi4]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h3, hc23, hlam, hphi, ht12, p62_1, u1ehi4]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h1, hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h1, h57, hc01, hc25, hlam, hphi, ht0b, ht5b, p62_1]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h1, h59, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p62_1, u1ehi4]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p62_1, u1ehi4]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h2, hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h56, hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h58, hlam, p62_1]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [hc14, hlam, hphi, p62_1, u1ehi4]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [hc15, hlam, hphi, p62_1, u1ehi0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h57, hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h2, h3, h56, h59, h60, h61, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p62_1, u4elo0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [h59, hlam, p62_0]
                      · have p62_0 := h62c.1
                        have p62_1 := h62c.2.1
                        have p62_2 := h62c.2.2.1
                        have p62_3 := h62c.2.2.2
                        linarith only [hlam, p62_0]
                    · linarith only [h2, h59, h61, hc34, hlam, hphi, u4elo0]
                  · linarith only [h3, h60, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h59, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h3, h56, h58, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h56, h57, hlam]
                · linarith only [h101, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h100, h3, h56, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo3]
          · linarith only [h56, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
      · linarith only [h1, h2, hc14, hlam, hphi, u1ehi2]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h108 | h108
    · linarith only [h0, h108, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h110 | h110
      · linarith only [h0, h110, hc12, hlam, hphi, u1ehi3]
      · linarith only [h110, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem n7l_sAA4_M_IR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
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
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_IR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
                · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                        · linarith only [h16, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h16, h7, hlam]
                      · linarith only [h15, h5, hlam]
                    · linarith only [h14, h9, hlam, p0_1]
                  · linarith only [h13, hc14, hlam, hphi, p0_1, u1ehi1]
                · linarith only [h12, h7, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · rcases p0_3 (m.d 1 2) (by simp) with h26 | h26
      · linarith only [h26, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h28 | h28
        · linarith only [h28, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h30 | h30
          · linarith only [h30, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h32 | h32
            · linarith only [h32, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h34 | h34
              · rcases m.htr 0 1 3 (by decide) (by decide) with h35 | h35
                · rcases m.htr 0 1 4 (by decide) (by decide) with h36 | h36
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h37 | h37
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                      · linarith only [h26, h38, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                        · linarith only [h38, h40, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h42 | h42
                          · linarith only [h42, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                          · linarith only [h30, h42, hlam]
                    · linarith only [h32, h37, hlam, p0_1]
                  · linarith only [h36, hc14, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h35, hlam, p0_0]
              · linarith only [h30, h34, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
    · linarith only [h25, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h50 | h50
    · rcases p0_3 (m.d 1 2) (by simp) with h51 | h51
      · linarith only [h51, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h53 | h53
        · linarith only [h53, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h55 | h55
          · linarith only [h55, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h57 | h57
            · linarith only [h57, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h59 | h59
              · rcases m.htr 0 1 3 (by decide) (by decide) with h60 | h60
                · rcases m.htr 0 1 4 (by decide) (by decide) with h61 | h61
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h62 | h62
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                        · linarith only [h51, h64, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
                          · linarith only [h53, h66, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
                              · linarith only [h69, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                              · linarith only [h57, h69, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                              · linarith only [h72, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                              · linarith only [h57, h72, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
                        · linarith only [h51, h75, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                          · linarith only [h53, h77, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                              · linarith only [h80, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                              · linarith only [h57, h80, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h83 | h83
                              · linarith only [h83, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                              · linarith only [h57, h83, hlam]
                    · linarith only [h62, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h61, hlam, p0_0]
                · linarith only [h60, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
              · linarith only [h59, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
    · linarith only [h50, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h91 | h91
    · rcases p0_3 (m.d 1 2) (by simp) with h92 | h92
      · linarith only [h92, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h94 | h94
        · linarith only [h94, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h96 | h96
          · linarith only [h96, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h98 | h98
            · linarith only [h98, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h100 | h100
              · rcases m.htr 0 1 3 (by decide) (by decide) with h101 | h101
                · rcases m.htr 0 1 4 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h103 | h103
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
                        · linarith only [h105, h92, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                          · linarith only [h104, h105, h107, h96, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
                            · linarith only [h109, h94, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                              · linarith only [h111, h96, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h113 | h113
                                · linarith only [h104, h105, h111, h113, hc24, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h104, h105, h113, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
                        · linarith only [h116, h92, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                          · linarith only [h118, h94, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h120 | h120
                            · linarith only [h120, h94, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                              · linarith only [h122, h96, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
                                · linarith only [h104, h118, h122, h124, hc24, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h116, h124, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h103, hlam, p0_0]
                  · linarith only [h102, hc14, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h101, h94, hlam, p0_1]
              · linarith only [h100, hc12, hlam, hphi, p0_1, u1ehi4]
    · linarith only [h91, hlam, p0_0]
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

theorem n7l_sAA4_M_IR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h2, h3, hlam, ht01, u1elo0]
      · linarith only [h2, hlam, hphi, ht01, u0ehi0, u1elo4]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi1, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n7l_sAA4_M_IR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases h0emin with h4 | h4 | h4 | h4 | h4
          · linarith only [h4, hlam, ht01, u1elo0]
          · linarith only [h0, h4, hlam, ht01, u1elo0]
          · linarith only [h1, h4, hlam, ht01, u1elo0]
          · linarith only [h2, h4, hlam, ht01, u1elo0]
          · linarith only [h3, h4, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, hphi, ht01, u0ehi0, u1elo4]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi1, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi1, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n7l_sAA4_M_IR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases h0emin with h4 | h4 | h4 | h4 | h4
          · linarith only [h4, hlam, ht01, u1elo0]
          · linarith only [h0, h4, hlam, ht01, u1elo0]
          · linarith only [h1, h4, hlam, ht01, u1elo0]
          · linarith only [h2, h4, hlam, ht01, u1elo0]
          · linarith only [h3, h4, hlam, ht01, u1elo0]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi1, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi1, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n7l_sAA4_M_IR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi8, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo3]

theorem n7l_sAA4_M_IR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA4_M_IR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA4_M_LI_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_LI_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_LI_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h21 | h21
    · linarith only [h21, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h21, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h28 | h28
    · linarith only [h28, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h28, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h39 | h39
    · linarith only [h39, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h39, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_LI_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
          · linarith only [h2, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
            · linarith only [h3, h5, h7, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · linarith only [h3, h7, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · linarith only [h2, hc01, hlam, hphi, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA4_M_LI_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases h0emin with h4 | h4 | h4 | h4 | h4
          · linarith only [h4, hlam, ht01, u1elo0]
          · linarith only [h0, h4, hlam, ht01, u1elo0]
          · linarith only [h1, h4, hlam, ht01, u1elo0]
          · linarith only [h2, h4, hlam, ht01, u1elo0]
          · linarith only [h3, h4, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA4_M_LI_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi4]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
    · linarith only [h1, hc01, hlam, hphi, u1elo4]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA4_M_LI_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem n7l_sAA4_M_LI_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA4_M_LI_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
  · linarith only [h0, hc13, hlam, hphi, u1ehi0]

theorem n7l_sAA4_M_LI_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h3, h5, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
            · linarith only [h0, h3, h4, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · linarith only [h4, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc12, hlam, hphi, u1ehi3]
    · linarith only [h12, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem n7l_sAA4_M_LI_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
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
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi4]
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

theorem n7l_sAA4_M_LI_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
          · linarith only [h0, h2, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
          · linarith only [h0, h2, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
          · linarith only [h0, h11, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
            · linarith only [h10, h13, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
          · linarith only [h0, h16, h2, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
            · linarith only [h1, h10, h18, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
              · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                · linarith only [h0, h10, h2, h21, hc24, hlam, hphi, ht12, u1ehi1]
                · linarith only [h0, h2, h21, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                · linarith only [h0, h10, h2, h24, hc24, hlam, hphi, ht12, u1ehi1]
                · linarith only [h0, h2, h24, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h28 | h28
    · linarith only [h0, h28, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
      · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
        · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
          · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
            · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
              · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                · linarith only [h30, h35, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                · linarith only [h30, h31, h35, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                · linarith only [h30, h38, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                · linarith only [h30, h31, h38, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · linarith only [h28, h30, h31, h33, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
          · linarith only [h0, h32, hc24, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
          · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
            · linarith only [h28, h31, h44, hc14, hlam, hphi, u1ehi0]
            · linarith only [h28, h44, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
          · linarith only [h30, h43, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h48 | h48
        · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
          · linarith only [h0, h30, h49, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h49, hc24, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
          · linarith only [h0, h30, h52, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h52, hc24, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAA4_M_LI_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
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
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
          · linarith only [h6, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h8 | h8
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h5, hlam]
                · linarith only [h10, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h14 | h14
              · rcases m.htr 0 1 3 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h5, hlam]
                · linarith only [h15, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h14, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h19 | h19
          · linarith only [h19, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h21 | h21
            · rcases m.htr 0 1 2 (by decide) (by decide) with h22 | h22
              · rcases m.htr 0 1 3 (by decide) (by decide) with h23 | h23
                · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h21, h25, hlam]
                    · linarith only [h25, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h19, h24, hlam, p0_1]
                · linarith only [h23, h5, hlam, p0_1]
              · linarith only [h22, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h31 | h31
              · rcases m.htr 0 1 3 (by decide) (by decide) with h32 | h32
                · rcases m.htr 0 1 4 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
                        · linarith only [h36, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
                        · linarith only [h36, h5, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                        · linarith only [h39, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
                        · linarith only [h39, h5, hlam]
                    · linarith only [h21, h34, hlam, p0_1]
                  · linarith only [h19, h33, hlam, p0_1]
                · linarith only [h32, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h31, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h47 | h47
    · rcases p0_3 (m.d 1 2) (by simp) with h48 | h48
      · rcases p0_3 (m.d 1 3) (by simp) with h49 | h49
        · linarith only [h49, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h51 | h51
          · linarith only [h51, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h48, h54, hlam]
              · linarith only [h54, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h57 | h57
              · linarith only [h48, h57, hlam]
              · linarith only [h57, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h60 | h60
        · linarith only [h60, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h62 | h62
          · linarith only [h48, h62, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h64 | h64
            · rcases m.htr 0 1 2 (by decide) (by decide) with h65 | h65
              · rcases m.htr 0 1 3 (by decide) (by decide) with h66 | h66
                · rcases m.htr 0 1 4 (by decide) (by decide) with h67 | h67
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h68 | h68
                    · linarith only [h64, h68, hlam]
                    · linarith only [h48, h68, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h62, h67, hlam, p0_1]
                · linarith only [h66, hlam, p0_0]
              · linarith only [h48, h65, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h74 | h74
              · rcases m.htr 0 1 3 (by decide) (by decide) with h75 | h75
                · rcases m.htr 0 1 4 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                        · linarith only [h48, h79, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                          · linarith only [h79, h81, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
                            · linarith only [h83, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                            · linarith only [h62, h83, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
                        · linarith only [h48, h86, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                          · linarith only [h86, h88, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                            · linarith only [h90, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                            · linarith only [h62, h90, hlam]
                    · linarith only [h64, h77, hlam, p0_1]
                  · linarith only [h76, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h75, hlam, p0_0]
              · linarith only [h74, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
    · linarith only [h47, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h98 | h98
    · rcases p0_3 (m.d 1 2) (by simp) with h99 | h99
      · rcases p0_3 (m.d 1 3) (by simp) with h100 | h100
        · rcases p0_3 (m.d 1 4) (by simp) with h101 | h101
          · linarith only [h101, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h103 | h103
            · rcases m.htr 0 1 2 (by decide) (by decide) with h104 | h104
              · linarith only [h104, h99, hlam]
              · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h107 | h107
              · linarith only [h107, h99, hlam]
              · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h110 | h110
          · linarith only [h110, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h112 | h112
            · rcases m.htr 0 1 2 (by decide) (by decide) with h113 | h113
              · linarith only [h113, h99, hlam]
              · linarith only [h100, h113, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h116 | h116
              · linarith only [h116, h99, hlam]
              · linarith only [h100, h116, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h119 | h119
        · rcases p0_3 (m.d 1 4) (by simp) with h120 | h120
          · linarith only [h120, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h122 | h122
            · rcases m.htr 0 1 2 (by decide) (by decide) with h123 | h123
              · rcases m.htr 0 1 3 (by decide) (by decide) with h124 | h124
                · linarith only [h119, h124, hlam]
                · linarith only [h124, h99, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h123, h99, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h128 | h128
              · rcases m.htr 0 1 3 (by decide) (by decide) with h129 | h129
                · linarith only [h119, h129, hlam]
                · linarith only [h129, h99, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h128, h99, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h133 | h133
          · linarith only [h133, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h135 | h135
            · rcases m.htr 0 1 2 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 1 3 (by decide) (by decide) with h137 | h137
                · rcases m.htr 0 1 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h139 | h139
                    · linarith only [h135, h139, hlam]
                    · linarith only [h139, h99, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h138, hlam, p0_0]
                · linarith only [h119, h137, hlam, p0_1]
              · linarith only [h136, h99, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h145 | h145
              · rcases m.htr 0 1 3 (by decide) (by decide) with h146 | h146
                · rcases m.htr 0 1 4 (by decide) (by decide) with h147 | h147
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h148 | h148
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h149 | h149
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
                        · linarith only [h150, h99, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                          · linarith only [h152, h99, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                            · linarith only [h119, h154, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
                              · linarith only [h154, h156, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                                · linarith only [h158, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                                · linarith only [h135, h158, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                        · linarith only [h161, h99, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h163 | h163
                          · linarith only [h163, h99, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h165 | h165
                            · linarith only [h119, h165, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h167 | h167
                              · linarith only [h165, h167, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h169 | h169
                                · linarith only [h149, h169, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                                · linarith only [h135, h169, hlam]
                    · linarith only [h148, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h147, hlam, p0_0]
                · linarith only [h146, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h145, h99, hlam, p0_1]
    · linarith only [h98, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h177 | h177
    · rcases p0_3 (m.d 1 2) (by simp) with h178 | h178
      · rcases p0_3 (m.d 1 3) (by simp) with h179 | h179
        · rcases p0_3 (m.d 1 4) (by simp) with h180 | h180
          · rcases p0_3 (m.d 1 5) (by simp) with h181 | h181
            · linarith only [h181, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h183 | h183
              · linarith only [h178, h183, hlam]
              · linarith only [h183, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h186 | h186
            · linarith only [h186, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h188 | h188
              · linarith only [h178, h188, hlam]
              · linarith only [h180, h188, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h191 | h191
          · linarith only [h179, h191, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h193 | h193
            · linarith only [h193, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h195 | h195
              · linarith only [h178, h195, hlam]
              · linarith only [h179, h195, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h198 | h198
        · rcases p0_3 (m.d 1 4) (by simp) with h199 | h199
          · linarith only [h178, h199, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h201 | h201
            · linarith only [h201, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h203 | h203
              · rcases m.htr 0 1 3 (by decide) (by decide) with h204 | h204
                · linarith only [h198, h204, hlam]
                · linarith only [h178, h204, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h178, h203, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h208 | h208
          · linarith only [h178, h208, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h210 | h210
            · linarith only [h210, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 1 3 (by decide) (by decide) with h213 | h213
                · rcases m.htr 0 1 4 (by decide) (by decide) with h214 | h214
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h215 | h215
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                        · linarith only [h178, h217, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                          · linarith only [h198, h217, h219, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                            · linarith only [h198, h221, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
                              · linarith only [h198, h223, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
                                · linarith only [h208, h225, hlam]
                                · linarith only [h216, h217, h221, h225, hc12, hlam, hphi, ht23, ht34, u4elo0]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h228 | h228
                        · linarith only [h178, h228, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
                          · linarith only [h198, h228, h230, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                            · linarith only [h198, h232, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h234 | h234
                              · linarith only [h198, h234, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
                                · linarith only [h208, h236, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                                  · linarith only [h216, h238, hc04, hlam, hphi, u4elo3]
                                  · linarith only [h228, h232, h238, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h215, hlam, p0_0]
                  · linarith only [h214, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3]
                · linarith only [h208, h213, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h178, h212, hlam, p0_1]
    · linarith only [h177, hlam, p0_0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h248 | h248
    · rcases p0_3 (m.d 1 2) (by simp) with h249 | h249
      · rcases p0_3 (m.d 1 3) (by simp) with h250 | h250
        · linarith only [h250, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h252 | h252
          · linarith only [h252, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h254 | h254
            · rcases m.htr 0 1 2 (by decide) (by decide) with h255 | h255
              · linarith only [h255, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h248, h255, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h258 | h258
              · linarith only [h258, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h248, h258, hlam]
      · linarith only [h249, hlam, p0_0]
    · linarith only [h248, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h263 | h263
    · rcases p0_3 (m.d 1 2) (by simp) with h264 | h264
      · rcases p0_3 (m.d 1 3) (by simp) with h265 | h265
        · rcases p0_3 (m.d 1 4) (by simp) with h266 | h266
          · linarith only [h266, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h268 | h268
            · rcases m.htr 0 1 2 (by decide) (by decide) with h269 | h269
              · linarith only [h269, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h263, h269, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · linarith only [h272, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h263, h272, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h275 | h275
          · linarith only [h275, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h277 | h277
            · rcases m.htr 0 1 2 (by decide) (by decide) with h278 | h278
              · linarith only [h265, h278, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h263, h278, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h281 | h281
              · linarith only [h265, h281, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h263, h281, hlam]
      · linarith only [h264, hlam, p0_0]
    · linarith only [h263, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h286 | h286
    · rcases p0_3 (m.d 1 2) (by simp) with h287 | h287
      · rcases p0_3 (m.d 1 3) (by simp) with h288 | h288
        · rcases p0_3 (m.d 1 4) (by simp) with h289 | h289
          · rcases p0_3 (m.d 1 5) (by simp) with h290 | h290
            · linarith only [h290, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h292 | h292
              · linarith only [h292, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h286, h292, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h295 | h295
            · linarith only [h295, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h297 | h297
              · linarith only [h289, h297, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h286, h297, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h300 | h300
          · linarith only [h288, h300, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h302 | h302
            · linarith only [h302, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h304 | h304
              · linarith only [h288, h304, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h286, h304, hlam]
      · linarith only [h287, hlam, p0_0]
    · linarith only [h286, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h310 | h310
    · rcases p0_3 (m.d 1 2) (by simp) with h311 | h311
      · linarith only [h311, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h313 | h313
        · rcases p0_3 (m.d 1 4) (by simp) with h314 | h314
          · linarith only [h314, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h316 | h316
            · rcases m.htr 0 1 2 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 1 3 (by decide) (by decide) with h318 | h318
                · linarith only [h318, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h310, h318, hlam]
              · linarith only [h317, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h322 | h322
              · rcases m.htr 0 1 3 (by decide) (by decide) with h323 | h323
                · linarith only [h323, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h310, h323, hlam]
              · linarith only [h322, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h313, hlam, p0_0]
    · linarith only [h310, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h330 | h330
    · rcases p0_3 (m.d 1 2) (by simp) with h331 | h331
      · rcases p0_3 (m.d 1 3) (by simp) with h332 | h332
        · rcases p0_3 (m.d 1 4) (by simp) with h333 | h333
          · linarith only [h333, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h335 | h335
            · rcases m.htr 0 1 2 (by decide) (by decide) with h336 | h336
              · linarith only [h331, h336, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h330, h336, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h339 | h339
              · linarith only [h331, h339, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h330, h339, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h332, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h343 | h343
        · rcases p0_3 (m.d 1 4) (by simp) with h344 | h344
          · linarith only [h344, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h346 | h346
            · rcases m.htr 0 1 2 (by decide) (by decide) with h347 | h347
              · rcases m.htr 0 1 3 (by decide) (by decide) with h348 | h348
                · linarith only [h331, h348, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h330, h348, hlam]
              · linarith only [h331, h347, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h352 | h352
              · rcases m.htr 0 1 3 (by decide) (by decide) with h353 | h353
                · linarith only [h331, h353, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h330, h353, hlam]
              · linarith only [h331, h352, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h343, hlam, p0_0]
    · linarith only [h330, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h359 | h359
    · rcases p0_3 (m.d 1 2) (by simp) with h360 | h360
      · rcases p0_3 (m.d 1 3) (by simp) with h361 | h361
        · rcases p0_3 (m.d 1 4) (by simp) with h362 | h362
          · rcases p0_3 (m.d 1 5) (by simp) with h363 | h363
            · linarith only [h363, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h365 | h365
              · linarith only [h360, h365, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h359, h365, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h368 | h368
            · linarith only [h368, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h370 | h370
              · linarith only [h360, h362, h370, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h359, h362, h370, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h361, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h374 | h374
        · rcases p0_3 (m.d 1 4) (by simp) with h375 | h375
          · linarith only [h360, h375, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h377 | h377
            · linarith only [h377, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h379 | h379
              · rcases m.htr 0 1 3 (by decide) (by decide) with h380 | h380
                · linarith only [h360, h380, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h359, h380, hlam]
              · linarith only [h360, h379, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h374, hlam, p0_0]
    · linarith only [h359, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h390 | h390
    · rcases p0_3 (m.d 1 2) (by simp) with h391 | h391
      · rcases p0_3 (m.d 1 3) (by simp) with h392 | h392
        · rcases p0_3 (m.d 1 4) (by simp) with h393 | h393
          · rcases p0_3 (m.d 1 5) (by simp) with h394 | h394
            · linarith only [h394, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h396 | h396
              · linarith only [h391, h396, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h390, h396, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · linarith only [h393, hlam, p0_0]
        · linarith only [h392, hc13, hlam, hphi, ht34, p0_1, u4elo1]
      · linarith only [h391, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
    · linarith only [h390, hc01, hlam, hphi, ht12, ht23, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h404 | h404
    · rcases p0_3 (m.d 1 2) (by simp) with h405 | h405
      · linarith only [h405, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h407 | h407
        · rcases p0_3 (m.d 1 4) (by simp) with h408 | h408
          · linarith only [h408, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h410 | h410
            · rcases m.htr 0 1 2 (by decide) (by decide) with h411 | h411
              · rcases m.htr 0 1 3 (by decide) (by decide) with h412 | h412
                · linarith only [h407, h412, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h404, h412, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h404, h411, hlam, p0_1]
            · linarith only [h410, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h417 | h417
          · linarith only [h417, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h419 | h419
            · rcases m.htr 0 1 2 (by decide) (by decide) with h420 | h420
              · rcases m.htr 0 1 3 (by decide) (by decide) with h421 | h421
                · rcases m.htr 0 1 4 (by decide) (by decide) with h422 | h422
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h423 | h423
                    · linarith only [h423, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h404, h423, hlam]
                  · linarith only [h417, h422, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h404, h407, h421, hlam, p0_1]
              · linarith only [h404, h420, hlam, p0_1]
            · linarith only [h419, hlam, p0_0]
    · linarith only [h404, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h431 | h431
    · rcases p0_3 (m.d 1 2) (by simp) with h432 | h432
      · rcases p0_3 (m.d 1 3) (by simp) with h433 | h433
        · linarith only [h433, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h435 | h435
          · linarith only [h435, hc13, hlam, hphi, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h437 | h437
            · rcases m.htr 0 1 2 (by decide) (by decide) with h438 | h438
              · linarith only [h432, h438, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h431, h438, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h437, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h442 | h442
        · linarith only [h442, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h444 | h444
          · linarith only [h432, h444, hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h446 | h446
            · rcases m.htr 0 1 2 (by decide) (by decide) with h447 | h447
              · rcases m.htr 0 1 3 (by decide) (by decide) with h448 | h448
                · rcases m.htr 0 1 4 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h450 | h450
                    · linarith only [h432, h450, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h431, h450, hlam]
                  · linarith only [h444, h449, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h431, h448, hlam, p0_1]
              · linarith only [h431, h432, h447, hlam, p0_1]
            · linarith only [h446, hlam, p0_0]
    · linarith only [h431, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h458 | h458
    · rcases p0_3 (m.d 1 2) (by simp) with h459 | h459
      · rcases p0_3 (m.d 1 3) (by simp) with h460 | h460
        · rcases p0_3 (m.d 1 4) (by simp) with h461 | h461
          · linarith only [h461, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h463 | h463
            · rcases m.htr 0 1 2 (by decide) (by decide) with h464 | h464
              · linarith only [h459, h464, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h458, h464, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h463, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h468 | h468
          · linarith only [h468, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h470 | h470
            · rcases m.htr 0 1 2 (by decide) (by decide) with h471 | h471
              · linarith only [h459, h460, h471, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h458, h460, h471, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h470, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h475 | h475
        · rcases p0_3 (m.d 1 4) (by simp) with h476 | h476
          · linarith only [h476, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h478 | h478
            · rcases m.htr 0 1 2 (by decide) (by decide) with h479 | h479
              · rcases m.htr 0 1 3 (by decide) (by decide) with h480 | h480
                · linarith only [h459, h475, h480, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h458, h459, h480, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h458, h459, h479, hlam, p0_1]
            · linarith only [h478, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h485 | h485
          · linarith only [h485, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h487 | h487
            · rcases m.htr 0 1 2 (by decide) (by decide) with h488 | h488
              · rcases m.htr 0 1 3 (by decide) (by decide) with h489 | h489
                · rcases m.htr 0 1 4 (by decide) (by decide) with h490 | h490
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h491 | h491
                    · linarith only [h459, h491, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h458, h491, hlam]
                  · linarith only [h490, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h458, h475, h489, hlam, p0_1]
              · linarith only [h458, h459, h488, hlam, p0_1]
            · linarith only [h487, hlam, p0_0]
    · linarith only [h458, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_LI_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
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
          · linarith only [h6, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h19 | h19
          · rcases p0_3 (m.d 1 5) (by simp) with h20 | h20
            · rcases m.htr 0 1 2 (by decide) (by decide) with h21 | h21
              · rcases m.htr 0 1 3 (by decide) (by decide) with h22 | h22
                · rcases m.htr 0 1 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h19, h23, hlam]
                  · linarith only [h23, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h22, h5, hlam, p0_1]
              · linarith only [h21, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h28 | h28
              · rcases m.htr 0 1 3 (by decide) (by decide) with h29 | h29
                · rcases m.htr 0 1 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h19, h30, hlam]
                  · linarith only [h30, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h29, h5, hlam, p0_1]
              · linarith only [h28, hlam, p0_0]
          · linarith only [h19, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · rcases p0_3 (m.d 1 2) (by simp) with h38 | h38
      · rcases p0_3 (m.d 1 3) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h41 | h41
          · rcases p0_3 (m.d 1 5) (by simp) with h42 | h42
            · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
              · linarith only [h38, h43, hlam]
              · linarith only [h43, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h46 | h46
              · linarith only [h38, h46, hlam]
              · linarith only [h46, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h41, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h50 | h50
        · linarith only [h50, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h52 | h52
          · rcases p0_3 (m.d 1 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · rcases m.htr 0 1 3 (by decide) (by decide) with h55 | h55
                · rcases m.htr 0 1 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h52, h56, hlam]
                  · linarith only [h38, h56, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h55, hlam, p0_0]
              · linarith only [h38, h54, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h61 | h61
              · rcases m.htr 0 1 3 (by decide) (by decide) with h62 | h62
                · rcases m.htr 0 1 4 (by decide) (by decide) with h63 | h63
                  · linarith only [h52, h63, hlam]
                  · linarith only [h38, h63, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h62, hlam, p0_0]
              · linarith only [h38, h61, hlam, p0_1]
          · linarith only [h52, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
    · linarith only [h37, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h71 | h71
    · rcases p0_3 (m.d 1 2) (by simp) with h72 | h72
      · rcases p0_3 (m.d 1 3) (by simp) with h73 | h73
        · rcases p0_3 (m.d 1 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 1 5) (by simp) with h75 | h75
            · linarith only [h75, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h77 | h77
              · linarith only [h72, h77, hlam]
              · linarith only [h77, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · linarith only [h74, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h81 | h81
          · rcases p0_3 (m.d 1 5) (by simp) with h82 | h82
            · linarith only [h82, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h84 | h84
              · linarith only [h72, h84, hlam]
              · linarith only [h73, h84, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h81, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h88 | h88
        · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
          · rcases p0_3 (m.d 1 5) (by simp) with h90 | h90
            · linarith only [h90, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h92 | h92
              · rcases m.htr 0 1 3 (by decide) (by decide) with h93 | h93
                · linarith only [h88, h93, hlam]
                · linarith only [h72, h93, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h72, h92, hlam, p0_1]
          · linarith only [h89, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h98 | h98
          · rcases p0_3 (m.d 1 5) (by simp) with h99 | h99
            · linarith only [h99, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h101 | h101
              · rcases m.htr 0 1 3 (by decide) (by decide) with h102 | h102
                · rcases m.htr 0 1 4 (by decide) (by decide) with h103 | h103
                  · linarith only [h103, h98, hlam]
                  · linarith only [h103, h88, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h102, h72, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h101, h72, hlam, p0_1]
          · linarith only [h98, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
    · linarith only [h71, hlam, p0_0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h112 | h112
    · rcases p0_3 (m.d 1 2) (by simp) with h113 | h113
      · rcases p0_3 (m.d 1 3) (by simp) with h114 | h114
        · linarith only [h114, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 1 5) (by simp) with h117 | h117
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · linarith only [h118, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h112, h118, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · linarith only [h121, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h112, h121, hlam]
          · linarith only [h116, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1, u4ehi1]
      · linarith only [h113, hlam, p0_0]
    · linarith only [h112, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h128 | h128
    · rcases p0_3 (m.d 1 2) (by simp) with h129 | h129
      · rcases p0_3 (m.d 1 3) (by simp) with h130 | h130
        · rcases p0_3 (m.d 1 4) (by simp) with h131 | h131
          · rcases p0_3 (m.d 1 5) (by simp) with h132 | h132
            · linarith only [h132, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
              · linarith only [h134, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h128, h134, hlam]
          · linarith only [h131, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 1 5) (by simp) with h139 | h139
            · linarith only [h139, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · linarith only [h130, h141, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h128, h141, hlam]
          · linarith only [h138, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1, u4ehi1]
      · linarith only [h129, hlam, p0_0]
    · linarith only [h128, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h148 | h148
    · rcases p0_3 (m.d 1 2) (by simp) with h149 | h149
      · linarith only [h149, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h151 | h151
        · rcases p0_3 (m.d 1 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 1 5) (by simp) with h153 | h153
            · rcases m.htr 0 1 2 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 1 3 (by decide) (by decide) with h155 | h155
                · linarith only [h155, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h148, h155, hlam]
              · linarith only [h154, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h159 | h159
              · rcases m.htr 0 1 3 (by decide) (by decide) with h160 | h160
                · linarith only [h160, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h148, h160, hlam]
              · linarith only [h159, hc01, hlam, hphi, p0_1, u1elo2]
          · linarith only [h152, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2, u4ehi1]
        · linarith only [h151, hlam, p0_0]
    · linarith only [h148, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h169 | h169
    · rcases p0_3 (m.d 1 2) (by simp) with h170 | h170
      · rcases p0_3 (m.d 1 3) (by simp) with h171 | h171
        · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
          · rcases p0_3 (m.d 1 5) (by simp) with h173 | h173
            · linarith only [h173, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h175 | h175
              · linarith only [h170, h175, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h169, h175, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · linarith only [h169, h172, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
        · linarith only [h171, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h180 | h180
        · rcases p0_3 (m.d 1 4) (by simp) with h181 | h181
          · rcases p0_3 (m.d 1 5) (by simp) with h182 | h182
            · linarith only [h182, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h184 | h184
              · rcases m.htr 0 1 3 (by decide) (by decide) with h185 | h185
                · linarith only [h170, h185, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h169, h185, hlam]
              · linarith only [h170, h184, hc01, hlam, hphi, p0_1, u1elo2]
          · linarith only [h181, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2, u4ehi1]
        · linarith only [h180, hlam, p0_0]
    · linarith only [h169, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h193 | h193
    · rcases p0_3 (m.d 1 2) (by simp) with h194 | h194
      · linarith only [h194, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h196 | h196
        · rcases p0_3 (m.d 1 4) (by simp) with h197 | h197
          · rcases p0_3 (m.d 1 5) (by simp) with h198 | h198
            · rcases m.htr 0 1 2 (by decide) (by decide) with h199 | h199
              · rcases m.htr 0 1 3 (by decide) (by decide) with h200 | h200
                · linarith only [h196, h200, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h193, h200, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h193, h199, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h204 | h204
              · rcases m.htr 0 1 3 (by decide) (by decide) with h205 | h205
                · linarith only [h196, h205, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h193, h205, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h193, h204, hlam, p0_1]
          · linarith only [h197, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h210 | h210
          · rcases p0_3 (m.d 1 5) (by simp) with h211 | h211
            · rcases m.htr 0 1 2 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 1 3 (by decide) (by decide) with h213 | h213
                · rcases m.htr 0 1 4 (by decide) (by decide) with h214 | h214
                  · linarith only [h214, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h193, h214, hlam]
                · linarith only [h196, h213, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h193, h212, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h219 | h219
              · rcases m.htr 0 1 3 (by decide) (by decide) with h220 | h220
                · rcases m.htr 0 1 4 (by decide) (by decide) with h221 | h221
                  · linarith only [h221, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h193, h221, hlam]
                · linarith only [h196, h220, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h193, h219, hlam, p0_1]
          · linarith only [h210, hlam, p0_0]
    · linarith only [h193, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h228 | h228
    · rcases p0_3 (m.d 1 2) (by simp) with h229 | h229
      · rcases p0_3 (m.d 1 3) (by simp) with h230 | h230
        · linarith only [h230, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h232 | h232
          · rcases p0_3 (m.d 1 5) (by simp) with h233 | h233
            · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
              · linarith only [h229, h234, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h228, h234, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h237 | h237
              · linarith only [h229, h237, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h228, h237, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h232, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h241 | h241
        · linarith only [h241, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h243 | h243
          · rcases p0_3 (m.d 1 5) (by simp) with h244 | h244
            · rcases m.htr 0 1 2 (by decide) (by decide) with h245 | h245
              · rcases m.htr 0 1 3 (by decide) (by decide) with h246 | h246
                · rcases m.htr 0 1 4 (by decide) (by decide) with h247 | h247
                  · linarith only [h229, h247, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h228, h247, hlam]
                · linarith only [h246, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h228, h229, h245, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h252 | h252
              · rcases m.htr 0 1 3 (by decide) (by decide) with h253 | h253
                · rcases m.htr 0 1 4 (by decide) (by decide) with h254 | h254
                  · linarith only [h229, h254, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h228, h254, hlam]
                · linarith only [h253, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h228, h252, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h243, hlam, p0_0]
    · linarith only [h228, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h262 | h262
    · rcases p0_3 (m.d 1 2) (by simp) with h263 | h263
      · rcases p0_3 (m.d 1 3) (by simp) with h264 | h264
        · rcases p0_3 (m.d 1 4) (by simp) with h265 | h265
          · rcases p0_3 (m.d 1 5) (by simp) with h266 | h266
            · linarith only [h266, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h268 | h268
              · linarith only [h263, h268, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h262, h268, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · linarith only [h265, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 1 5) (by simp) with h273 | h273
            · linarith only [h273, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h275 | h275
              · linarith only [h263, h264, h275, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h262, h264, h275, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h279 | h279
        · rcases p0_3 (m.d 1 4) (by simp) with h280 | h280
          · rcases p0_3 (m.d 1 5) (by simp) with h281 | h281
            · linarith only [h281, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h283 | h283
              · rcases m.htr 0 1 3 (by decide) (by decide) with h284 | h284
                · linarith only [h263, h279, h284, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h262, h263, h284, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h262, h263, h283, hlam, p0_1]
          · linarith only [h280, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h289 | h289
          · rcases p0_3 (m.d 1 5) (by simp) with h290 | h290
            · linarith only [h290, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h292 | h292
              · rcases m.htr 0 1 3 (by decide) (by decide) with h293 | h293
                · rcases m.htr 0 1 4 (by decide) (by decide) with h294 | h294
                  · linarith only [h263, h294, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h262, h294, hlam]
                · linarith only [h279, h293, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h262, h263, h292, hlam, p0_1]
          · linarith only [h289, hlam, p0_0]
    · linarith only [h262, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h302 | h302
    · rcases p0_3 (m.d 1 2) (by simp) with h303 | h303
      · linarith only [h303, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h305 | h305
        · rcases p0_3 (m.d 1 4) (by simp) with h306 | h306
          · rcases p0_3 (m.d 1 5) (by simp) with h307 | h307
            · rcases m.htr 0 1 2 (by decide) (by decide) with h308 | h308
              · rcases m.htr 0 1 3 (by decide) (by decide) with h309 | h309
                · linarith only [h305, h309, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h302, h309, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h302, h308, hlam, p0_1]
            · linarith only [h307, hlam, p0_0]
          · linarith only [h302, h306, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h315 | h315
          · rcases p0_3 (m.d 1 5) (by simp) with h316 | h316
            · rcases m.htr 0 1 2 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 1 3 (by decide) (by decide) with h318 | h318
                · rcases m.htr 0 1 4 (by decide) (by decide) with h319 | h319
                  · linarith only [h315, h319, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h302, h319, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h302, h305, h318, hlam, p0_1]
              · linarith only [h302, h317, hlam, p0_1]
            · linarith only [h316, hlam, p0_0]
          · linarith only [h302, h315, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
    · linarith only [h302, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h327 | h327
    · rcases p0_3 (m.d 1 2) (by simp) with h328 | h328
      · rcases p0_3 (m.d 1 3) (by simp) with h329 | h329
        · linarith only [h329, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h331 | h331
          · rcases p0_3 (m.d 1 5) (by simp) with h332 | h332
            · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
              · linarith only [h328, h333, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h327, h333, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h332, hlam, p0_0]
          · linarith only [h327, h331, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h338 | h338
        · linarith only [h338, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h340 | h340
          · rcases p0_3 (m.d 1 5) (by simp) with h341 | h341
            · rcases m.htr 0 1 2 (by decide) (by decide) with h342 | h342
              · rcases m.htr 0 1 3 (by decide) (by decide) with h343 | h343
                · rcases m.htr 0 1 4 (by decide) (by decide) with h344 | h344
                  · linarith only [h328, h340, h344, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h327, h328, h344, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h327, h343, hlam, p0_1]
              · linarith only [h327, h328, h342, hlam, p0_1]
            · linarith only [h341, hlam, p0_0]
          · linarith only [h327, h340, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
    · linarith only [h327, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo4, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_LI_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA4_M_LI_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA4_M_LI_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi7 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi7, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo2]

theorem n7l_sAA4_M_LR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1bigk := hb1.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht34, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_LR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1bigk := hb1.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
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
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h21 | h21
    · linarith only [h21, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h21, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h28 | h28
    · linarith only [h28, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h28, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h39 | h39
    · linarith only [h39, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h39, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA4_M_LR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

theorem n7l_sAA4_M_LR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

theorem n7l_sAA4_M_LR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

theorem n7l_sAA4_M_LR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem n7l_sAA4_M_LR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
  · linarith only [h0, hc14, hlam, hphi, u1ehi0]

theorem n7l_sAA4_M_LR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA4_M_LR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h2, h5, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
            · linarith only [h0, h2, h3, h5, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · linarith only [h0, h2, h3, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
    · linarith only [h0, h1, hc15, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc13, hlam, hphi, u1ehi4]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
      · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
        · linarith only [h12, h15, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5, u4elo1]
        · linarith only [h15, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
      · linarith only [h14, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]

theorem n7l_sAA4_M_LR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
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
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi4]
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
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
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
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
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
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
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

theorem n7l_sAA4_M_LR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.2.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · linarith only [h0, h3, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · linarith only [h0, h3, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h12, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
              · linarith only [h1, h14, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
              · linarith only [h11, h14, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
            · linarith only [h0, h17, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h1, h11, h19, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                · linarith only [h11, h21, h3, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                · linarith only [h17, h19, h2, h21, h3, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi6, u0elo0, u1ehi1]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h26 | h26
    · linarith only [h0, h26, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
      · linarith only [h0, h28, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
        · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
            · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
              · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                · linarith only [h30, h34, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                · linarith only [h30, h31, h34, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
              · linarith only [h30, h31, h33, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
            · linarith only [h0, h32, hc24, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
            · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
              · linarith only [h31, h39, h40, hc12, hlam, hphi, ht01, u0ehi8]
              · linarith only [h26, h40, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
            · linarith only [h30, h39, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h44 | h44
          · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
            · linarith only [h0, h30, h45, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h45, hc24, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
            · linarith only [h0, h30, h48, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h48, hc24, hlam, hphi, ht01, ht12, u0ehi5]

theorem n7l_sAA4_M_LR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h6, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h4, h7, h9, hc23, hlam, hphi, ht34, u4elo0]
              · linarith only [h0, h3, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
              · linarith only [h0, h13, h2, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h15, h17, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h17, h4, hc34, hlam, hphi, u4elo0]
                  · linarith only [h13, h16, h4, hc12, hlam, hphi, ht23, ht34, u4elo0]
                · linarith only [h15, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h24 | h24
        · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
          · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
            · linarith only [h2, h24, h25, h26, hlam, hphi, ht01, u0ehi9, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
              · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                  · linarith only [h1, h26, h28, h30, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h25, h29, h30, hc34, hlam, hphi, u4elo0]
                · linarith only [h2, h29, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · linarith only [h2, h24, h28, hc12, hc23, hlam, hphi]
          · linarith only [h25, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
        · linarith only [h24, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
    · linarith only [h1, hlam, hphi, ht01, u0ehi5, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem n7l_sAA4_M_LR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h2, h8, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
              · rcases h1bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  rcases p10_3 (m.d 0 1) (by simp) with h12 | h12
                  · rcases p10_3 (m.d 1 2) (by simp) with h13 | h13
                    · linarith only [h13, hlam, p10_0]
                    · rcases p10_3 (m.d 1 3) (by simp) with h15 | h15
                      · linarith only [h1, h15, hlam]
                      · rcases p10_3 (m.d 1 4) (by simp) with h17 | h17
                        · linarith only [h17, h2, hlam]
                        · linarith only [h17, h4, hlam]
                  · linarith only [h12, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  rcases p10_3 (m.d 0 1) (by simp) with h21 | h21
                  · rcases p10_3 (m.d 1 2) (by simp) with h22 | h22
                    · linarith only [h0, h22, hlam]
                    · rcases p10_3 (m.d 1 3) (by simp) with h24 | h24
                      · linarith only [h24, hlam, p10_0]
                      · rcases p10_3 (m.d 1 4) (by simp) with h26 | h26
                        · linarith only [h2, h26, hlam]
                        · linarith only [h26, h6, hlam]
                  · linarith only [h21, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0, u4ehi1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0, u4ehi1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10_1, u1elo0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h4, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h4, h8, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h1, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h6, hc12, hc34, hlam, hphi, ht23, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h6, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h6, h8, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h2, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hc12, hc45, hlam, hphi, ht23, ht34, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hc13, hc45, hlam, hphi, ht34, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10_1, u1elo0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10_1, u1elo0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, hlam, hphi, ht01, ht0b, ht45, ht5b, p10_1, u1elo0, u4ehi1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
        · linarith only [h3, hlam, hphi, ht01, u0ehi5, u1elo4]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi6, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem n7l_sAA4_M_LR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi9 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi9, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo4]

theorem n7l_sAA4_M_LR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA4_M_LR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi8, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo3]

end R2N4
