import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAA5_H_I_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h5elo := hb5.1
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h5, hlam]
                · linarith only [h10, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h9, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h14 | h14
            · linarith only [h14, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
              · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                · linarith only [h17, h5, hlam]
                · linarith only [h17, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h16, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 1 5) (by simp) with h22 | h22
            · linarith only [h22, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h21, h26, hlam]
                  · linarith only [h26, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h25, h5, hlam, p0_1]
              · linarith only [h24, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h31 | h31
            · linarith only [h31, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 1 3 (by decide) (by decide) with h34 | h34
                · rcases m.htr 0 1 4 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                      · linarith only [h37, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h37, h5, hlam]
                    · linarith only [h31, h36, hlam, p0_1]
                  · linarith only [h21, h35, hlam, p0_1]
                · linarith only [h34, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h33, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h45 | h45
    · rcases p0_3 (m.d 1 2) (by simp) with h46 | h46
      · rcases p0_3 (m.d 1 3) (by simp) with h47 | h47
        · linarith only [h47, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h49 | h49
          · rcases p0_3 (m.d 1 5) (by simp) with h50 | h50
            · linarith only [h50, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h52 | h52
              · linarith only [h46, h52, hlam]
              · linarith only [h52, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h55 | h55
            · linarith only [h55, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h57 | h57
              · linarith only [h46, h57, hlam]
              · linarith only [h57, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h60 | h60
        · linarith only [h60, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h62 | h62
          · rcases p0_3 (m.d 1 5) (by simp) with h63 | h63
            · linarith only [h46, h63, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h65 | h65
              · rcases m.htr 0 1 3 (by decide) (by decide) with h66 | h66
                · rcases m.htr 0 1 4 (by decide) (by decide) with h67 | h67
                  · linarith only [h62, h67, hlam]
                  · linarith only [h46, h67, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h66, hlam, p0_0]
              · linarith only [h46, h65, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h72 | h72
            · linarith only [h46, h72, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h74 | h74
              · rcases m.htr 0 1 3 (by decide) (by decide) with h75 | h75
                · rcases m.htr 0 1 4 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                      · linarith only [h46, h78, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                        · linarith only [h78, h80, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                          · linarith only [h78, h82, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                            · linarith only [h84, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                            · linarith only [h62, h84, hlam]
                    · linarith only [h72, h77, hlam, p0_1]
                  · linarith only [h76, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h75, hlam, p0_0]
              · linarith only [h74, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
    · linarith only [h45, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h92 | h92
    · rcases p0_3 (m.d 1 2) (by simp) with h93 | h93
      · rcases p0_3 (m.d 1 3) (by simp) with h94 | h94
        · rcases p0_3 (m.d 1 4) (by simp) with h95 | h95
          · linarith only [h95, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h97 | h97
            · linarith only [h97, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h99 | h99
              · linarith only [h93, h99, hlam]
              · linarith only [h99, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
          · linarith only [h102, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h104 | h104
            · linarith only [h104, h94, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
              · linarith only [h106, h93, hlam]
              · linarith only [h106, h94, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h109 | h109
        · rcases p0_3 (m.d 1 4) (by simp) with h110 | h110
          · linarith only [h110, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h112 | h112
            · linarith only [h112, h93, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h114 | h114
              · rcases m.htr 0 1 3 (by decide) (by decide) with h115 | h115
                · linarith only [h109, h115, hlam]
                · linarith only [h115, h93, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h114, h93, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h121 | h121
            · linarith only [h121, h93, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h123 | h123
              · rcases m.htr 0 1 3 (by decide) (by decide) with h124 | h124
                · rcases m.htr 0 1 4 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h126 | h126
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                      · linarith only [h127, h93, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                        · linarith only [h129, h93, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                          · linarith only [h109, h127, h131, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                            · linarith only [h109, h133, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                              · linarith only [h133, h135, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                                · linarith only [h137, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                · linarith only [h121, h137, hlam]
                    · linarith only [h126, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h125, hlam, p0_0]
                · linarith only [h124, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h123, h93, hlam, p0_1]
    · linarith only [h92, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h145 | h145
    · rcases p0_3 (m.d 1 2) (by simp) with h146 | h146
      · rcases p0_3 (m.d 1 3) (by simp) with h147 | h147
        · rcases p0_3 (m.d 1 4) (by simp) with h148 | h148
          · rcases p0_3 (m.d 1 5) (by simp) with h149 | h149
            · linarith only [h149, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h151 | h151
              · linarith only [h146, h151, hlam]
              · linarith only [h151, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h154 | h154
            · linarith only [h154, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h156 | h156
              · linarith only [h146, h156, hlam]
              · linarith only [h148, h156, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 1 5) (by simp) with h160 | h160
            · linarith only [h160, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h162 | h162
              · linarith only [h146, h162, hlam]
              · linarith only [h147, h162, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h165 | h165
            · linarith only [h165, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h167 | h167
              · linarith only [h146, h167, hlam]
              · linarith only [h147, h167, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h170 | h170
        · rcases p0_3 (m.d 1 4) (by simp) with h171 | h171
          · rcases p0_3 (m.d 1 5) (by simp) with h172 | h172
            · linarith only [h172, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h174 | h174
              · rcases m.htr 0 1 3 (by decide) (by decide) with h175 | h175
                · linarith only [h170, h175, hlam]
                · linarith only [h146, h175, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h146, h174, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h179 | h179
            · linarith only [h179, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h181 | h181
              · rcases m.htr 0 1 3 (by decide) (by decide) with h182 | h182
                · linarith only [h170, h182, hlam]
                · linarith only [h146, h182, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h146, h181, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h186 | h186
          · rcases p0_3 (m.d 1 5) (by simp) with h187 | h187
            · linarith only [h187, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h189 | h189
              · rcases m.htr 0 1 3 (by decide) (by decide) with h190 | h190
                · rcases m.htr 0 1 4 (by decide) (by decide) with h191 | h191
                  · linarith only [h186, h191, hlam]
                  · linarith only [h146, h191, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h170, h190, hlam, p0_1]
              · linarith only [h146, h189, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h196 | h196
            · linarith only [h196, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h198 | h198
              · rcases m.htr 0 1 3 (by decide) (by decide) with h199 | h199
                · rcases m.htr 0 1 4 (by decide) (by decide) with h200 | h200
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h201 | h201
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                      · linarith only [h146, h202, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
                        · linarith only [h170, h202, h204, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                          · linarith only [h146, h206, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                            · linarith only [h170, h208, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                              · linarith only [h170, h210, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
                                · linarith only [h186, h212, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h216 | h216
                                      · linarith only [h202, h208, h212, h214, h216, hc12, hc23, hlam, hphi]
                                      · linarith only [h202, h208, h216, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                    · linarith only [h202, h215, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h220 | h220
                                    · linarith only [h202, h210, h214, h220, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h202, h220, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h201, hlam, p0_0]
                  · linarith only [h200, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                · linarith only [h186, h199, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h146, h198, hlam, p0_1]
    · linarith only [h145, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h230 | h230
    · rcases p0_3 (m.d 1 2) (by simp) with h231 | h231
      · rcases p0_3 (m.d 1 3) (by simp) with h232 | h232
        · linarith only [h232, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h234 | h234
          · rcases p0_3 (m.d 1 5) (by simp) with h235 | h235
            · linarith only [h235, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h237 | h237
              · linarith only [h237, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h230, h237, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h240 | h240
            · linarith only [h240, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h242 | h242
              · linarith only [h242, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h230, h242, hlam]
      · linarith only [h231, hlam, p0_0]
    · linarith only [h230, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h247 | h247
    · rcases p0_3 (m.d 1 2) (by simp) with h248 | h248
      · rcases p0_3 (m.d 1 3) (by simp) with h249 | h249
        · rcases p0_3 (m.d 1 4) (by simp) with h250 | h250
          · linarith only [h250, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h252 | h252
            · linarith only [h252, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h254 | h254
              · linarith only [h254, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h247, h254, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h257 | h257
          · linarith only [h257, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h259 | h259
            · linarith only [h249, h259, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h261 | h261
              · linarith only [h249, h261, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h247, h261, hlam]
      · linarith only [h248, hlam, p0_0]
    · linarith only [h247, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h266 | h266
    · rcases p0_3 (m.d 1 2) (by simp) with h267 | h267
      · rcases p0_3 (m.d 1 3) (by simp) with h268 | h268
        · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
          · rcases p0_3 (m.d 1 5) (by simp) with h270 | h270
            · linarith only [h270, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · linarith only [h272, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h266, h272, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h275 | h275
            · linarith only [h275, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h277 | h277
              · linarith only [h269, h277, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h266, h277, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h280 | h280
          · rcases p0_3 (m.d 1 5) (by simp) with h281 | h281
            · linarith only [h281, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h283 | h283
              · linarith only [h268, h283, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h266, h283, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h286 | h286
            · linarith only [h286, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h288 | h288
              · linarith only [h268, h288, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h266, h288, hlam]
      · linarith only [h267, hlam, p0_0]
    · linarith only [h266, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h294 | h294
    · rcases p0_3 (m.d 1 2) (by simp) with h295 | h295
      · linarith only [h295, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h297 | h297
        · rcases p0_3 (m.d 1 4) (by simp) with h298 | h298
          · rcases p0_3 (m.d 1 5) (by simp) with h299 | h299
            · linarith only [h299, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h301 | h301
              · rcases m.htr 0 1 3 (by decide) (by decide) with h302 | h302
                · linarith only [h302, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h294, h302, hlam]
              · linarith only [h301, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h306 | h306
            · linarith only [h306, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h308 | h308
              · rcases m.htr 0 1 3 (by decide) (by decide) with h309 | h309
                · linarith only [h309, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h294, h309, hlam]
              · linarith only [h308, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h297, hlam, p0_0]
    · linarith only [h294, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h316 | h316
    · rcases p0_3 (m.d 1 2) (by simp) with h317 | h317
      · rcases p0_3 (m.d 1 3) (by simp) with h318 | h318
        · rcases p0_3 (m.d 1 4) (by simp) with h319 | h319
          · linarith only [h319, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h321 | h321
            · linarith only [h321, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h323 | h323
              · linarith only [h317, h323, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h316, h323, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h318, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h327 | h327
        · rcases p0_3 (m.d 1 4) (by simp) with h328 | h328
          · linarith only [h328, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h330 | h330
            · linarith only [h317, h330, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h332 | h332
              · rcases m.htr 0 1 3 (by decide) (by decide) with h333 | h333
                · linarith only [h317, h333, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h316, h333, hlam]
              · linarith only [h317, h332, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h327, hlam, p0_0]
    · linarith only [h316, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h339 | h339
    · rcases p0_3 (m.d 1 2) (by simp) with h340 | h340
      · rcases p0_3 (m.d 1 3) (by simp) with h341 | h341
        · rcases p0_3 (m.d 1 4) (by simp) with h342 | h342
          · rcases p0_3 (m.d 1 5) (by simp) with h343 | h343
            · linarith only [h343, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h345 | h345
              · linarith only [h340, h345, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h339, h345, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h348 | h348
            · linarith only [h348, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h350 | h350
              · linarith only [h340, h342, h350, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h339, h342, h350, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h341, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h354 | h354
        · rcases p0_3 (m.d 1 4) (by simp) with h355 | h355
          · rcases p0_3 (m.d 1 5) (by simp) with h356 | h356
            · linarith only [h356, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h358 | h358
              · rcases m.htr 0 1 3 (by decide) (by decide) with h359 | h359
                · linarith only [h340, h359, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h339, h359, hlam]
              · linarith only [h340, h358, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h363 | h363
            · linarith only [h363, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h365 | h365
              · rcases m.htr 0 1 3 (by decide) (by decide) with h366 | h366
                · linarith only [h340, h366, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h339, h366, hlam]
              · linarith only [h340, h365, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h354, hlam, p0_0]
    · linarith only [h339, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h373 | h373
    · rcases p0_3 (m.d 1 2) (by simp) with h374 | h374
      · linarith only [h374, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h376 | h376
        · rcases p0_3 (m.d 1 4) (by simp) with h377 | h377
          · rcases p0_3 (m.d 1 5) (by simp) with h378 | h378
            · linarith only [h378, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h380 | h380
              · rcases m.htr 0 1 3 (by decide) (by decide) with h381 | h381
                · linarith only [h376, h381, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h373, h381, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h373, h380, hlam, p0_1]
          · linarith only [h377, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h386 | h386
          · rcases p0_3 (m.d 1 5) (by simp) with h387 | h387
            · linarith only [h387, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h389 | h389
              · rcases m.htr 0 1 3 (by decide) (by decide) with h390 | h390
                · rcases m.htr 0 1 4 (by decide) (by decide) with h391 | h391
                  · linarith only [h391, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h373, h391, hlam]
                · linarith only [h376, h390, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h373, h389, hlam, p0_1]
          · linarith only [h386, hlam, p0_0]
    · linarith only [h373, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h398 | h398
    · rcases p0_3 (m.d 1 2) (by simp) with h399 | h399
      · rcases p0_3 (m.d 1 3) (by simp) with h400 | h400
        · linarith only [h400, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h402 | h402
          · rcases p0_3 (m.d 1 5) (by simp) with h403 | h403
            · linarith only [h403, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h405 | h405
              · linarith only [h399, h405, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h398, h405, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h402, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h409 | h409
        · linarith only [h409, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h411 | h411
          · rcases p0_3 (m.d 1 5) (by simp) with h412 | h412
            · linarith only [h399, h412, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h414 | h414
              · rcases m.htr 0 1 3 (by decide) (by decide) with h415 | h415
                · rcases m.htr 0 1 4 (by decide) (by decide) with h416 | h416
                  · linarith only [h399, h416, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h398, h416, hlam]
                · linarith only [h415, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h398, h399, h414, hlam, p0_1]
          · linarith only [h411, hlam, p0_0]
    · linarith only [h398, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h424 | h424
    · rcases p0_3 (m.d 1 2) (by simp) with h425 | h425
      · rcases p0_3 (m.d 1 3) (by simp) with h426 | h426
        · rcases p0_3 (m.d 1 4) (by simp) with h427 | h427
          · rcases p0_3 (m.d 1 5) (by simp) with h428 | h428
            · linarith only [h428, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h430 | h430
              · linarith only [h425, h430, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h424, h430, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · linarith only [h427, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h434 | h434
          · rcases p0_3 (m.d 1 5) (by simp) with h435 | h435
            · linarith only [h435, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h437 | h437
              · linarith only [h425, h426, h437, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h424, h426, h437, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h434, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h441 | h441
        · rcases p0_3 (m.d 1 4) (by simp) with h442 | h442
          · rcases p0_3 (m.d 1 5) (by simp) with h443 | h443
            · linarith only [h443, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h445 | h445
              · rcases m.htr 0 1 3 (by decide) (by decide) with h446 | h446
                · linarith only [h425, h441, h446, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h424, h425, h446, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h424, h425, h445, hlam, p0_1]
          · linarith only [h442, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h451 | h451
          · rcases p0_3 (m.d 1 5) (by simp) with h452 | h452
            · linarith only [h452, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h454 | h454
              · rcases m.htr 0 1 3 (by decide) (by decide) with h455 | h455
                · rcases m.htr 0 1 4 (by decide) (by decide) with h456 | h456
                  · linarith only [h425, h456, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h424, h456, hlam]
                · linarith only [h441, h455, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h424, h425, h454, hlam, p0_1]
          · linarith only [h451, hlam, p0_0]
    · linarith only [h424, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_I_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
                · linarith only [h5, h9, hlam]
                · linarith only [h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h8, hlam, p0_0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
                · linarith only [h16, h5, hlam]
                · linarith only [h16, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h15, hlam, p0_0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases m.htr 0 1 2 (by decide) (by decide) with h23 | h23
              · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 0 1 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h21, h25, hlam]
                  · linarith only [h25, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h23, h24, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h23, hlam, p0_0]
            · linarith only [h22, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h31 | h31
            · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h31, h35, hlam]
                    · linarith only [h35, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h32, h34, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h32, h33, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h32, hlam, p0_0]
            · linarith only [h31, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · rcases p0_3 (m.d 0 2) (by simp) with h44 | h44
      · rcases p0_3 (m.d 0 3) (by simp) with h45 | h45
        · linarith only [h45, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h47 | h47
          · rcases p0_3 (m.d 0 5) (by simp) with h48 | h48
            · rcases m.htr 0 1 2 (by decide) (by decide) with h49 | h49
              · linarith only [h44, h49, hlam]
              · linarith only [h49, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h48, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h44, h54, hlam]
              · linarith only [h54, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h53, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h58 | h58
        · linarith only [h58, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 0 5) (by simp) with h61 | h61
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · rcases m.htr 0 1 3 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
                  · linarith only [h60, h64, hlam]
                  · linarith only [h44, h64, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h63, hlam, p0_0]
              · linarith only [h44, h62, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h61, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h70 | h70
            · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
              · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h70, h74, hlam]
                    · linarith only [h74, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h44, h71, h73, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h72, hlam, p0_0]
              · linarith only [h44, h71, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h70, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h43, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h82 | h82
    · rcases p0_3 (m.d 0 2) (by simp) with h83 | h83
      · rcases p0_3 (m.d 0 3) (by simp) with h84 | h84
        · rcases p0_3 (m.d 0 4) (by simp) with h85 | h85
          · linarith only [h85, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h87 | h87
            · rcases m.htr 0 1 2 (by decide) (by decide) with h88 | h88
              · linarith only [h83, h88, hlam]
              · linarith only [h88, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h87, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
          · linarith only [h92, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h94 | h94
            · rcases m.htr 0 1 2 (by decide) (by decide) with h95 | h95
              · linarith only [h83, h95, hlam]
              · linarith only [h84, h95, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h94, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h99 | h99
        · rcases p0_3 (m.d 0 4) (by simp) with h100 | h100
          · linarith only [h100, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h102 | h102
            · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
              · rcases m.htr 0 1 3 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h99, hlam]
                · linarith only [h104, h83, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h103, h83, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h102, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h109 | h109
          · linarith only [h109, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h111 | h111
            · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 1 3 (by decide) (by decide) with h113 | h113
                · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h111, h115, hlam]
                    · linarith only [h115, h99, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h114, hlam, p0_0]
                · linarith only [h112, h113, h83, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h83, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h111, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h82, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h124 | h124
    · linarith only [h124, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h126 | h126
      · rcases p0_3 (m.d 0 3) (by simp) with h127 | h127
        · rcases p0_3 (m.d 0 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 0 5) (by simp) with h129 | h129
            · rcases m.htr 0 1 2 (by decide) (by decide) with h130 | h130
              · linarith only [h130, hlam, p0_0]
              · linarith only [h130, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h129, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · rcases m.htr 0 1 2 (by decide) (by decide) with h135 | h135
              · linarith only [h135, hlam, p0_0]
              · linarith only [h135, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h134, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
          · rcases p0_3 (m.d 0 5) (by simp) with h140 | h140
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · linarith only [h141, hlam, p0_0]
              · linarith only [h141, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h140, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h145 | h145
            · rcases m.htr 0 1 2 (by decide) (by decide) with h146 | h146
              · linarith only [h146, hlam, p0_0]
              · linarith only [h146, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h145, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h126, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h152 | h152
    · rcases p0_3 (m.d 0 2) (by simp) with h153 | h153
      · rcases p0_3 (m.d 0 3) (by simp) with h154 | h154
        · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 0 5) (by simp) with h157 | h157
            · rcases m.htr 0 1 2 (by decide) (by decide) with h158 | h158
              · rcases m.htr 0 1 3 (by decide) (by decide) with h159 | h159
                · rcases m.htr 0 1 4 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h162 | h162
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h163 | h163
                        · linarith only [h156, h163, hlam]
                        · linarith only [h163, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h162, hlam, p0_0]
                    · linarith only [h158, h159, h161, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h158, h159, h160, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h158, h159, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h158, hlam]
            · linarith only [h157, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h172 | h172
            · rcases m.htr 0 1 2 (by decide) (by decide) with h173 | h173
              · rcases m.htr 0 1 3 (by decide) (by decide) with h174 | h174
                · rcases m.htr 0 1 4 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h177 | h177
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h178 | h178
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h179 | h179
                          · linarith only [h172, h179, hlam]
                          · linarith only [h179, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h174, h178, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h177, hlam, p0_0]
                    · linarith only [h173, h174, h176, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h173, h174, h175, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h173, h174, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h173, hlam]
            · linarith only [h152, h172, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h153, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h190 | h190
      · rcases p0_3 (m.d 0 3) (by simp) with h191 | h191
        · linarith only [h191, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h193 | h193
          · rcases p0_3 (m.d 0 5) (by simp) with h194 | h194
            · rcases m.htr 0 1 2 (by decide) (by decide) with h195 | h195
              · linarith only [h152, h195, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h195, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h194, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h199 | h199
            · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
              · linarith only [h152, h200, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h200, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h199, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h190, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h205 | h205
    · rcases p0_3 (m.d 0 2) (by simp) with h206 | h206
      · rcases p0_3 (m.d 0 3) (by simp) with h207 | h207
        · rcases p0_3 (m.d 0 4) (by simp) with h208 | h208
          · linarith only [h208, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h210 | h210
            · rcases m.htr 0 1 2 (by decide) (by decide) with h211 | h211
              · rcases m.htr 0 1 3 (by decide) (by decide) with h212 | h212
                · rcases m.htr 0 1 4 (by decide) (by decide) with h213 | h213
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h215 | h215
                      · linarith only [h207, h215, hlam]
                      · linarith only [h215, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h211, h213, h214, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h211, h213, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h211, h212, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h205, h211, hlam]
            · linarith only [h210, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h223 | h223
          · linarith only [h223, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h225 | h225
            · rcases m.htr 0 1 2 (by decide) (by decide) with h226 | h226
              · rcases m.htr 0 1 3 (by decide) (by decide) with h227 | h227
                · rcases m.htr 0 1 4 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h225, h232, hlam]
                          · linarith only [h207, h232, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h231, hlam, p0_0]
                      · linarith only [h207, h227, h230, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h207, h226, h227, h229, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h207, h226, h227, h228, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h207, h226, h227, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h205, h226, hlam]
            · linarith only [h225, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h206, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h243 | h243
      · rcases p0_3 (m.d 0 3) (by simp) with h244 | h244
        · rcases p0_3 (m.d 0 4) (by simp) with h245 | h245
          · linarith only [h245, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h247 | h247
            · rcases m.htr 0 1 2 (by decide) (by decide) with h248 | h248
              · linarith only [h205, h248, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h205, h248, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h247, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h252 | h252
          · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h254 | h254
            · rcases m.htr 0 1 2 (by decide) (by decide) with h255 | h255
              · linarith only [h205, h255, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h205, h255, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h254, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h243, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h261 | h261
    · linarith only [h261, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h263 | h263
      · rcases p0_3 (m.d 0 3) (by simp) with h264 | h264
        · rcases p0_3 (m.d 0 4) (by simp) with h265 | h265
          · rcases p0_3 (m.d 0 5) (by simp) with h266 | h266
            · rcases m.htr 0 1 2 (by decide) (by decide) with h267 | h267
              · linarith only [h267, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h267, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h263, h266, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h271 | h271
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · linarith only [h263, h272, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h272, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h263, h271, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h264, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h277 | h277
        · rcases p0_3 (m.d 0 4) (by simp) with h278 | h278
          · rcases p0_3 (m.d 0 5) (by simp) with h279 | h279
            · rcases m.htr 0 1 2 (by decide) (by decide) with h280 | h280
              · linarith only [h280, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h280, hlam]
            · linarith only [h279, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h284 | h284
            · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
              · linarith only [h285, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h285, hlam]
            · linarith only [h284, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h277, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h290 | h290
    · rcases p0_3 (m.d 0 2) (by simp) with h291 | h291
      · linarith only [h291, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h293 | h293
        · rcases p0_3 (m.d 0 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
            · rcases m.htr 0 1 2 (by decide) (by decide) with h296 | h296
              · rcases m.htr 0 1 3 (by decide) (by decide) with h297 | h297
                · rcases m.htr 0 1 4 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h300 | h300
                      · linarith only [h300, hlam, p0_0]
                      · linarith only [h300, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h296, h297, h299, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h296, h297, h298, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h290, h297, hlam]
              · linarith only [h290, h296, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h290, h295, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h308 | h308
            · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
              · rcases m.htr 0 1 3 (by decide) (by decide) with h310 | h310
                · rcases m.htr 0 1 4 (by decide) (by decide) with h311 | h311
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h312 | h312
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
                      · linarith only [h313, hlam, p0_0]
                      · linarith only [h313, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h309, h310, h312, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h309, h310, h311, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h290, h310, hlam]
              · linarith only [h290, h309, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h290, h308, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h293, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h322 | h322
      · linarith only [h322, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h324 | h324
        · rcases p0_3 (m.d 0 4) (by simp) with h325 | h325
          · rcases p0_3 (m.d 0 5) (by simp) with h326 | h326
            · rcases m.htr 0 1 2 (by decide) (by decide) with h327 | h327
              · linarith only [h290, h327, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h329 | h329
                · linarith only [h327, h329, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h327, h329, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h326, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h333 | h333
            · rcases m.htr 0 1 2 (by decide) (by decide) with h334 | h334
              · linarith only [h290, h334, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h336 | h336
                · linarith only [h334, h336, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h334, h336, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h333, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h324, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h342 | h342
    · rcases p0_3 (m.d 0 2) (by simp) with h343 | h343
      · rcases p0_3 (m.d 0 3) (by simp) with h344 | h344
        · rcases p0_3 (m.d 0 4) (by simp) with h345 | h345
          · linarith only [h345, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h347 | h347
            · rcases m.htr 0 1 2 (by decide) (by decide) with h348 | h348
              · rcases m.htr 0 1 3 (by decide) (by decide) with h349 | h349
                · rcases m.htr 0 1 4 (by decide) (by decide) with h350 | h350
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h351 | h351
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h352 | h352
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h353 | h353
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h354 | h354
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
                              · linarith only [h347, h356, hlam]
                              · linarith only [h350, h356, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                            · linarith only [h355, hlam, p0_0]
                          · linarith only [h350, h352, h354, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                        · linarith only [h350, h352, h353, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h343, h352, hlam]
                    · linarith only [h349, h350, h351, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h343, h348, h350, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h342, h349, hlam]
              · linarith only [h342, h348, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h342, h347, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h344, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h369 | h369
        · rcases p0_3 (m.d 0 4) (by simp) with h370 | h370
          · linarith only [h370, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h372 | h372
            · rcases m.htr 0 1 2 (by decide) (by decide) with h373 | h373
              · rcases m.htr 0 1 3 (by decide) (by decide) with h374 | h374
                · rcases m.htr 0 1 4 (by decide) (by decide) with h375 | h375
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h376 | h376
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h377 | h377
                      · linarith only [h343, h374, h377, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h343, h373, h377, hc12, hc23, hlam, hphi, p0_1]
                    · linarith only [h343, h373, h374, h376, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h343, h373, h374, h375, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h342, h374, hlam]
              · linarith only [h342, h343, h373, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h342, h372, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h369, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h386 | h386
      · rcases p0_3 (m.d 0 3) (by simp) with h387 | h387
        · rcases p0_3 (m.d 0 4) (by simp) with h388 | h388
          · linarith only [h388, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h390 | h390
            · rcases m.htr 0 1 2 (by decide) (by decide) with h391 | h391
              · linarith only [h342, h391, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h342, h386, h391, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h386, h390, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h387, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h396 | h396
        · rcases p0_3 (m.d 0 4) (by simp) with h397 | h397
          · linarith only [h397, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h399 | h399
            · rcases m.htr 0 1 2 (by decide) (by decide) with h400 | h400
              · linarith only [h342, h400, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h402 | h402
                · linarith only [h386, h400, h402, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h386, h400, h402, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h399, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h396, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h408 | h408
    · linarith only [h408, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h410 | h410
      · rcases p0_3 (m.d 0 3) (by simp) with h411 | h411
        · rcases p0_3 (m.d 0 4) (by simp) with h412 | h412
          · rcases p0_3 (m.d 0 5) (by simp) with h413 | h413
            · rcases m.htr 0 1 2 (by decide) (by decide) with h414 | h414
              · linarith only [h410, h414, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h414, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h410, h413, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h412, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h419 | h419
          · rcases p0_3 (m.d 0 5) (by simp) with h420 | h420
            · rcases m.htr 0 1 2 (by decide) (by decide) with h421 | h421
              · linarith only [h410, h421, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h421, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h410, h420, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h419, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h426 | h426
        · rcases p0_3 (m.d 0 4) (by simp) with h427 | h427
          · rcases p0_3 (m.d 0 5) (by simp) with h428 | h428
            · rcases m.htr 0 1 2 (by decide) (by decide) with h429 | h429
              · linarith only [h429, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h429, hlam]
            · linarith only [h428, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h427, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h434 | h434
          · rcases p0_3 (m.d 0 5) (by simp) with h435 | h435
            · rcases m.htr 0 1 2 (by decide) (by decide) with h436 | h436
              · linarith only [h436, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h436, hlam]
            · linarith only [h435, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h434, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h441 | h441
    · rcases p0_3 (m.d 0 2) (by simp) with h442 | h442
      · linarith only [h442, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h444 | h444
        · rcases p0_3 (m.d 0 4) (by simp) with h445 | h445
          · rcases p0_3 (m.d 0 5) (by simp) with h446 | h446
            · rcases m.htr 0 1 2 (by decide) (by decide) with h447 | h447
              · rcases m.htr 0 1 3 (by decide) (by decide) with h448 | h448
                · rcases m.htr 0 1 4 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h451 | h451
                      · linarith only [h444, h448, h451, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h444, h451, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h447, h449, h450, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h441, h449, hlam]
                · linarith only [h441, h447, h448, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h441, h447, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h441, h446, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h445, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h460 | h460
          · rcases p0_3 (m.d 0 5) (by simp) with h461 | h461
            · rcases m.htr 0 1 2 (by decide) (by decide) with h462 | h462
              · rcases m.htr 0 1 3 (by decide) (by decide) with h463 | h463
                · rcases m.htr 0 1 4 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h465 | h465
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h466 | h466
                      · linarith only [h464, h466, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h444, h466, hlam]
                    · linarith only [h464, h465, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h441, h464, hlam]
                · linarith only [h441, h462, h463, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h441, h462, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h441, h461, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h460, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h475 | h475
      · linarith only [h475, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h477 | h477
        · rcases p0_3 (m.d 0 4) (by simp) with h478 | h478
          · rcases p0_3 (m.d 0 5) (by simp) with h479 | h479
            · rcases m.htr 0 1 2 (by decide) (by decide) with h480 | h480
              · linarith only [h441, h480, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h482 | h482
                · linarith only [h480, h482, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h477, h480, h482, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h479, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h478, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h487 | h487
          · rcases p0_3 (m.d 0 5) (by simp) with h488 | h488
            · rcases m.htr 0 1 2 (by decide) (by decide) with h489 | h489
              · linarith only [h441, h489, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h491 | h491
                · linarith only [h489, h491, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h493 | h493
                  · linarith only [h489, h493, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h489, h493, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h488, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h487, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h498 | h498
    · rcases p0_3 (m.d 0 2) (by simp) with h499 | h499
      · rcases p0_3 (m.d 0 3) (by simp) with h500 | h500
        · linarith only [h500, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h502 | h502
          · rcases p0_3 (m.d 0 5) (by simp) with h503 | h503
            · rcases m.htr 0 1 2 (by decide) (by decide) with h504 | h504
              · rcases m.htr 0 1 3 (by decide) (by decide) with h505 | h505
                · rcases m.htr 0 1 4 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h507 | h507
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h508 | h508
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h509 | h509
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h510 | h510
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h511 | h511
                            · linarith only [h511, hlam, p0_0]
                            · linarith only [h505, h511, hc13, hc34, hlam, hphi, p0_1]
                          · linarith only [h505, h509, h510, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h499, h509, hlam]
                      · linarith only [h499, h505, h508, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h505, h506, h507, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h498, h506, hlam]
                · linarith only [h498, h505, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h498, h504, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h498, h503, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h502, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h523 | h523
        · linarith only [h523, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h525 | h525
          · rcases p0_3 (m.d 0 5) (by simp) with h526 | h526
            · rcases m.htr 0 1 2 (by decide) (by decide) with h527 | h527
              · rcases m.htr 0 1 3 (by decide) (by decide) with h528 | h528
                · rcases m.htr 0 1 4 (by decide) (by decide) with h529 | h529
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h530 | h530
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h531 | h531
                      · linarith only [h499, h531, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h533 | h533
                        · linarith only [h529, h531, h533, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h527, h531, h533, hc12, hc24, hlam, hphi, p0_1]
                    · linarith only [h529, h530, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h498, h529, hlam]
                · linarith only [h498, h499, h527, h528, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h498, h499, h527, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h498, h526, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h525, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h542 | h542
      · rcases p0_3 (m.d 0 3) (by simp) with h543 | h543
        · linarith only [h543, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h545 | h545
          · rcases p0_3 (m.d 0 5) (by simp) with h546 | h546
            · rcases m.htr 0 1 2 (by decide) (by decide) with h547 | h547
              · linarith only [h498, h547, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h498, h542, h547, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h542, h546, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h545, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h552 | h552
        · linarith only [h552, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h554 | h554
          · rcases p0_3 (m.d 0 5) (by simp) with h555 | h555
            · rcases m.htr 0 1 2 (by decide) (by decide) with h556 | h556
              · linarith only [h498, h556, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h558 | h558
                · linarith only [h498, h558, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h560 | h560
                  · linarith only [h542, h556, h560, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h542, h556, h560, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h555, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h554, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h567 | h567
    · linarith only [h567, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h569 | h569
      · rcases p0_3 (m.d 0 3) (by simp) with h570 | h570
        · rcases p0_3 (m.d 0 4) (by simp) with h571 | h571
          · rcases p0_3 (m.d 0 5) (by simp) with h572 | h572
            · rcases m.htr 0 1 2 (by decide) (by decide) with h573 | h573
              · linarith only [h569, h573, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h573, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h572, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h577 | h577
            · rcases m.htr 0 1 2 (by decide) (by decide) with h578 | h578
              · linarith only [h569, h578, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h578, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h577, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h582 | h582
          · rcases p0_3 (m.d 0 5) (by simp) with h583 | h583
            · rcases m.htr 0 1 2 (by decide) (by decide) with h584 | h584
              · linarith only [h569, h584, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h584, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h583, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h588 | h588
            · rcases m.htr 0 1 2 (by decide) (by decide) with h589 | h589
              · linarith only [h569, h589, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h589, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h588, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h593 | h593
        · rcases p0_3 (m.d 0 4) (by simp) with h594 | h594
          · rcases p0_3 (m.d 0 5) (by simp) with h595 | h595
            · rcases m.htr 0 1 2 (by decide) (by decide) with h596 | h596
              · linarith only [h593, h596, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h596, hlam]
            · linarith only [h595, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h600 | h600
            · rcases m.htr 0 1 2 (by decide) (by decide) with h601 | h601
              · linarith only [h593, h601, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h601, hlam]
            · linarith only [h600, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h605 | h605
          · rcases p0_3 (m.d 0 5) (by simp) with h606 | h606
            · rcases m.htr 0 1 2 (by decide) (by decide) with h607 | h607
              · linarith only [h605, h607, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h607, hlam]
            · linarith only [h606, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h611 | h611
            · rcases m.htr 0 1 2 (by decide) (by decide) with h612 | h612
              · linarith only [h612, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h612, hlam]
            · linarith only [h611, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h616 | h616
    · rcases p0_3 (m.d 0 2) (by simp) with h617 | h617
      · linarith only [h617, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h619 | h619
        · rcases p0_3 (m.d 0 4) (by simp) with h620 | h620
          · rcases p0_3 (m.d 0 5) (by simp) with h621 | h621
            · rcases m.htr 0 1 2 (by decide) (by decide) with h622 | h622
              · rcases m.htr 0 1 3 (by decide) (by decide) with h623 | h623
                · rcases m.htr 0 1 4 (by decide) (by decide) with h624 | h624
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h625 | h625
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h626 | h626
                      · linarith only [h619, h623, h626, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h626, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h616, h625, hlam]
                  · linarith only [h616, h622, h624, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h622, h623, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h622, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h621, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h634 | h634
            · rcases m.htr 0 1 2 (by decide) (by decide) with h635 | h635
              · rcases m.htr 0 1 3 (by decide) (by decide) with h636 | h636
                · rcases m.htr 0 1 4 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h638 | h638
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h639 | h639
                      · linarith only [h619, h636, h639, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h639, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h616, h638, hlam]
                  · linarith only [h619, h635, h636, h637, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h635, h636, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h635, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h634, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h647 | h647
          · rcases p0_3 (m.d 0 5) (by simp) with h648 | h648
            · rcases m.htr 0 1 2 (by decide) (by decide) with h649 | h649
              · rcases m.htr 0 1 3 (by decide) (by decide) with h650 | h650
                · rcases m.htr 0 1 4 (by decide) (by decide) with h651 | h651
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h652 | h652
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h653 | h653
                      · linarith only [h647, h651, h653, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h653, hlam]
                    · linarith only [h616, h652, hlam]
                  · linarith only [h616, h651, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h649, h650, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h649, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h648, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h661 | h661
            · rcases m.htr 0 1 2 (by decide) (by decide) with h662 | h662
              · rcases m.htr 0 1 3 (by decide) (by decide) with h663 | h663
                · rcases m.htr 0 1 4 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h665 | h665
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h666 | h666
                      · linarith only [h665, h666, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h666, hlam]
                    · linarith only [h616, h665, hlam]
                  · linarith only [h616, h664, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h662, h663, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h662, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h661, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h674 | h674
      · linarith only [h674, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h676 | h676
        · rcases p0_3 (m.d 0 4) (by simp) with h677 | h677
          · rcases p0_3 (m.d 0 5) (by simp) with h678 | h678
            · rcases m.htr 0 1 2 (by decide) (by decide) with h679 | h679
              · linarith only [h616, h679, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h681 | h681
                · linarith only [h676, h679, h681, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h676, h679, h681, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h678, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h685 | h685
            · rcases m.htr 0 1 2 (by decide) (by decide) with h686 | h686
              · linarith only [h616, h686, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h688 | h688
                · linarith only [h676, h686, h688, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h676, h686, h688, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h685, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h692 | h692
          · rcases p0_3 (m.d 0 5) (by simp) with h693 | h693
            · rcases m.htr 0 1 2 (by decide) (by decide) with h694 | h694
              · linarith only [h616, h694, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h696 | h696
                · linarith only [h692, h694, h696, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h698 | h698
                  · linarith only [h692, h694, h698, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h692, h694, h698, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h693, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h702 | h702
            · rcases m.htr 0 1 2 (by decide) (by decide) with h703 | h703
              · linarith only [h616, h703, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h705 | h705
                · linarith only [h703, h705, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h707 | h707
                  · linarith only [h703, h707, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h709 | h709
                    · linarith only [h703, h709, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                    · linarith only [h703, h709, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h702, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h713 | h713
    · rcases p0_3 (m.d 0 2) (by simp) with h714 | h714
      · rcases p0_3 (m.d 0 3) (by simp) with h715 | h715
        · linarith only [h715, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h717 | h717
          · rcases p0_3 (m.d 0 5) (by simp) with h718 | h718
            · rcases m.htr 0 1 2 (by decide) (by decide) with h719 | h719
              · rcases m.htr 0 1 3 (by decide) (by decide) with h720 | h720
                · rcases m.htr 0 1 4 (by decide) (by decide) with h721 | h721
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h722 | h722
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h723 | h723
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h724 | h724
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h725 | h725
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h726 | h726
                            · linarith only [h717, h719, h724, h726, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                            · linarith only [h717, h726, hc03, hc34, hlam, hphi, p0_1]
                          · linarith only [h714, h725, hlam]
                        · linarith only [h714, h720, h724, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h714, h720, h723, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h713, h722, hlam]
                  · linarith only [h713, h720, h721, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h714, h719, h720, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h719, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h718, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h737 | h737
            · rcases m.htr 0 1 2 (by decide) (by decide) with h738 | h738
              · rcases m.htr 0 1 3 (by decide) (by decide) with h739 | h739
                · rcases m.htr 0 1 4 (by decide) (by decide) with h740 | h740
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h741 | h741
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h743 | h743
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h744 | h744
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h745 | h745
                            · linarith only [h738, h744, h745, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                            · linarith only [h717, h745, hlam]
                          · linarith only [h714, h744, hlam]
                        · linarith only [h714, h743, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h714, h739, h742, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h713, h741, hlam]
                  · linarith only [h713, h739, h740, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h714, h738, h739, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h738, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h737, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h756 | h756
        · linarith only [h756, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h758 | h758
          · rcases p0_3 (m.d 0 5) (by simp) with h759 | h759
            · rcases m.htr 0 1 2 (by decide) (by decide) with h760 | h760
              · rcases m.htr 0 1 3 (by decide) (by decide) with h761 | h761
                · rcases m.htr 0 1 4 (by decide) (by decide) with h762 | h762
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h763 | h763
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h764 | h764
                      · linarith only [h714, h764, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h766 | h766
                        · linarith only [h758, h762, h764, h766, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h758, h764, h766, hc02, hc24, hlam, hphi, p0_1]
                    · linarith only [h713, h763, hlam]
                  · linarith only [h713, h714, h760, h762, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h713, h714, h760, h761, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h714, h760, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h759, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h774 | h774
            · rcases m.htr 0 1 2 (by decide) (by decide) with h775 | h775
              · rcases m.htr 0 1 3 (by decide) (by decide) with h776 | h776
                · rcases m.htr 0 1 4 (by decide) (by decide) with h777 | h777
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h778 | h778
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h779 | h779
                      · linarith only [h714, h779, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h781 | h781
                        · linarith only [h778, h779, h781, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h783 | h783
                          · linarith only [h778, h779, h783, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                          · linarith only [h779, h783, hc02, hc25, hlam, hphi, p0_1]
                    · linarith only [h713, h778, hlam]
                  · linarith only [h713, h777, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h713, h714, h775, h776, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h714, h775, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h774, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h791 | h791
      · rcases p0_3 (m.d 0 3) (by simp) with h792 | h792
        · linarith only [h792, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h794 | h794
          · rcases p0_3 (m.d 0 5) (by simp) with h795 | h795
            · rcases m.htr 0 1 2 (by decide) (by decide) with h796 | h796
              · linarith only [h713, h791, h796, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h791, h796, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h795, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h800 | h800
            · rcases m.htr 0 1 2 (by decide) (by decide) with h801 | h801
              · linarith only [h713, h791, h801, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h791, h801, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h800, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h805 | h805
        · linarith only [h805, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h807 | h807
          · rcases p0_3 (m.d 0 5) (by simp) with h808 | h808
            · rcases m.htr 0 1 2 (by decide) (by decide) with h809 | h809
              · linarith only [h713, h807, h809, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h811 | h811
                · linarith only [h713, h811, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h813 | h813
                  · linarith only [h791, h807, h809, h813, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h791, h807, h809, h813, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h808, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h817 | h817
            · rcases m.htr 0 1 2 (by decide) (by decide) with h818 | h818
              · linarith only [h713, h818, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h820 | h820
                · linarith only [h713, h820, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h822 | h822
                  · linarith only [h791, h818, h822, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h824 | h824
                    · linarith only [h791, h818, h824, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                    · linarith only [h791, h818, h824, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h817, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h828 | h828
    · rcases p0_3 (m.d 0 2) (by simp) with h829 | h829
      · rcases p0_3 (m.d 0 3) (by simp) with h830 | h830
        · rcases p0_3 (m.d 0 4) (by simp) with h831 | h831
          · linarith only [h831, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h833 | h833
            · rcases m.htr 0 1 2 (by decide) (by decide) with h834 | h834
              · rcases m.htr 0 1 3 (by decide) (by decide) with h835 | h835
                · rcases m.htr 0 1 4 (by decide) (by decide) with h836 | h836
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h837 | h837
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h841 | h841
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h842 | h842
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h843 | h843
                                · linarith only [h843, hlam, p0_0]
                                · linarith only [h836, h843, hc14, hc45, hlam, hphi, p0_1]
                              · linarith only [h830, h842, hlam]
                            · linarith only [h830, h836, h841, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                          · linarith only [h829, h840, hlam]
                        · linarith only [h830, h836, h838, h839, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h829, h836, h838, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h828, h837, hlam]
                  · linarith only [h828, h836, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h829, h834, h835, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h828, h834, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h833, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h856 | h856
          · linarith only [h856, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h858 | h858
            · rcases m.htr 0 1 2 (by decide) (by decide) with h859 | h859
              · rcases m.htr 0 1 3 (by decide) (by decide) with h860 | h860
                · rcases m.htr 0 1 4 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h862 | h862
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h863 | h863
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h864 | h864
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h865 | h865
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h866 | h866
                            · linarith only [h830, h866, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h868 | h868
                              · linarith only [h859, h865, h866, h868, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                              · linarith only [h866, h868, hc03, hc35, hlam, hphi, p0_1]
                          · linarith only [h829, h865, hlam]
                        · linarith only [h829, h864, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h829, h830, h860, h863, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h828, h862, hlam]
                  · linarith only [h828, h830, h860, h861, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h829, h830, h859, h860, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h830, h859, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h858, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h879 | h879
        · rcases p0_3 (m.d 0 4) (by simp) with h880 | h880
          · linarith only [h880, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h882 | h882
            · rcases m.htr 0 1 2 (by decide) (by decide) with h883 | h883
              · rcases m.htr 0 1 3 (by decide) (by decide) with h884 | h884
                · rcases m.htr 0 1 4 (by decide) (by decide) with h885 | h885
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h886 | h886
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h887 | h887
                      · linarith only [h829, h879, h884, h887, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h829, h879, h887, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h828, h886, hlam]
                  · linarith only [h829, h879, h883, h884, h885, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h828, h829, h883, h884, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h829, h883, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h882, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h895 | h895
          · linarith only [h895, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h897 | h897
            · rcases m.htr 0 1 2 (by decide) (by decide) with h898 | h898
              · rcases m.htr 0 1 3 (by decide) (by decide) with h899 | h899
                · rcases m.htr 0 1 4 (by decide) (by decide) with h900 | h900
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h902 | h902
                      · linarith only [h829, h901, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h904 | h904
                        · linarith only [h829, h904, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h906 | h906
                          · linarith only [h879, h901, h902, h906, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                          · linarith only [h879, h902, h906, hc02, hc25, hlam, hphi, p0_1]
                    · linarith only [h828, h901, hlam]
                  · linarith only [h828, h829, h898, h900, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h828, h829, h898, h899, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h829, h898, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h897, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h914 | h914
      · rcases p0_3 (m.d 0 3) (by simp) with h915 | h915
        · rcases p0_3 (m.d 0 4) (by simp) with h916 | h916
          · linarith only [h916, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h918 | h918
            · rcases m.htr 0 1 2 (by decide) (by decide) with h919 | h919
              · linarith only [h828, h914, h919, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h914, h919, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h918, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h923 | h923
          · linarith only [h923, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h925 | h925
            · rcases m.htr 0 1 2 (by decide) (by decide) with h926 | h926
              · linarith only [h828, h914, h926, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h914, h926, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h925, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h930 | h930
        · rcases p0_3 (m.d 0 4) (by simp) with h931 | h931
          · linarith only [h931, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h933 | h933
            · rcases m.htr 0 1 2 (by decide) (by decide) with h934 | h934
              · linarith only [h828, h930, h934, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h936 | h936
                · linarith only [h914, h930, h934, h936, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h914, h930, h934, h936, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h933, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h940 | h940
          · linarith only [h940, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h942 | h942
            · rcases m.htr 0 1 2 (by decide) (by decide) with h943 | h943
              · linarith only [h828, h943, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h945 | h945
                · linarith only [h914, h943, h945, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h947 | h947
                  · linarith only [h828, h947, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h949 | h949
                    · linarith only [h914, h943, h949, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                    · linarith only [h914, h943, h949, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h942, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_I_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5elo := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc13, hlam, hphi, p0_1, u1ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · linarith only [h7, hc14, hlam, hphi, p0_1, u1ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h9 | h9
            · linarith only [h9, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
                · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                                      · linarith only [h17, h23, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                      · linarith only [h17, h20, h23, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                    · linarith only [h22, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                                  · linarith only [h20, h21, hc34, hlam, hphi, ht45, u5elo3]
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                                      · linarith only [h20, h28, h30, hc23, hlam, hphi, ht12, u1ehi4]
                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                                        · linarith only [h18, h30, h32, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                        · linarith only [h20, h28, h32, hc23, hc34, hlam, hphi]
                                    · linarith only [h20, h28, h29, hc35, hlam, hphi, u5elo4]
                                  · linarith only [h28, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                              · linarith only [h19, h9, hlam]
                            · linarith only [h18, h7, hlam]
                          · linarith only [h17, h5, hlam]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                                · linarith only [h16, h40, h43, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                                      · linarith only [h12, h16, h45, h47, hc23, hlam, hphi, ht12, u1ehi4]
                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                                        · linarith only [h41, h47, h49, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                        · linarith only [h12, h16, h45, h49, hc23, hc34, hlam, hphi]
                                    · linarith only [h43, h45, h46, hc35, hlam, hphi, u5elo4]
                                  · linarith only [h45, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                              · linarith only [h42, h9, hlam]
                            · linarith only [h41, h7, hlam]
                          · linarith only [h40, h5, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h57 | h57
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                          · linarith only [h15, h58, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                          · linarith only [h5, h58, hlam]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                          · linarith only [h11, h15, h61, hlam]
                          · linarith only [h5, h61, hlam]
                    · linarith only [h14, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
                  · linarith only [h13, h7, hlam, p0_1]
                · linarith only [h12, hc13, hlam, hphi, p0_1, u1ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h69 | h69
    · rcases p0_3 (m.d 1 2) (by simp) with h70 | h70
      · linarith only [h70, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h72 | h72
        · linarith only [h72, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h74 | h74
          · linarith only [h74, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h76 | h76
            · linarith only [h76, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h78 | h78
              · rcases m.htr 0 1 3 (by decide) (by decide) with h79 | h79
                · rcases m.htr 0 1 4 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                          · linarith only [h70, h84, hlam]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
                                          · linarith only [h84, h86, h93, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                          · linarith only [h84, h86, h90, h93, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                        · linarith only [h84, h86, h90, h92, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                      · linarith only [h84, h86, h90, h91, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                    · linarith only [h90, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                                  · linarith only [h76, h89, hlam]
                                · linarith only [h74, h88, hlam]
                              · linarith only [h87, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h105 | h105
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                                            · linarith only [h103, h109, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                            · linarith only [h103, h105, h109, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                          · linarith only [h102, h103, h105, h108, h86, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
                                        · linarith only [h102, h106, h107, h86, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                      · linarith only [h102, h106, h78, h82, h83, h84, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                                    · linarith only [h105, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                                  · linarith only [h104, h76, hlam]
                                · linarith only [h103, h74, hlam]
                              · linarith only [h102, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h119 | h119
                          · linarith only [h119, h70, hlam]
                          · linarith only [h119, h82, h83, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h122 | h122
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                          · linarith only [h123, h70, hlam]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                                          · linarith only [h123, h125, h132, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                          · linarith only [h123, h125, h129, h132, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                        · linarith only [h131, h82, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                      · linarith only [h125, h129, h130, h78, h82, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                    · linarith only [h129, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                                  · linarith only [h128, h76, hlam]
                                · linarith only [h127, h74, hlam]
                              · linarith only [h125, h126, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo2]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h141 | h141
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h142 | h142
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h143 | h143
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                                            · linarith only [h142, h148, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                            · linarith only [h142, h144, h148, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                          · linarith only [h125, h142, h144, h147, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                                        · linarith only [h141, h146, h78, h82, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                      · linarith only [h141, h145, h78, h82, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                    · linarith only [h144, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                                  · linarith only [h143, h76, hlam]
                                · linarith only [h142, h74, hlam]
                              · linarith only [h141, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                          · linarith only [h158, h70, hlam]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h160 | h160
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                                · linarith only [h122, h162, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                · linarith only [h162, h74, hlam]
                              · linarith only [h160, h161, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo2]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h166 | h166
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h167 | h167
                                · linarith only [h122, h167, h79, hlam]
                                · linarith only [h167, h74, hlam]
                              · linarith only [h166, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                    · linarith only [h81, hc15, hlam, hphi, p0_1, u1ehi2]
                  · linarith only [h80, hc14, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h79, hlam, p0_0]
              · linarith only [h78, hc12, hlam, hphi, p0_1, u1ehi2]
    · linarith only [h69, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h176 | h176
    · rcases p0_3 (m.d 1 2) (by simp) with h177 | h177
      · linarith only [h177, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h179 | h179
        · linarith only [h179, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h181 | h181
          · linarith only [h181, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h183 | h183
            · linarith only [h183, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h185 | h185
              · rcases m.htr 0 1 3 (by decide) (by decide) with h186 | h186
                · rcases m.htr 0 1 4 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h188 | h188
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h189 | h189
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h190 | h190
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                            · linarith only [h177, h192, hlam]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                                · linarith only [h179, h195, hlam]
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h198 | h198
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
                                      · linarith only [h191, h192, h195, h197, h199, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                                        · linarith only [h185, h189, h190, h191, h192, h199, h201, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                        · linarith only [h195, h197, h201, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                    · linarith only [h183, h198, hlam]
                                  · linarith only [h197, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                              · linarith only [h194, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h207 | h207
                            · linarith only [h177, h207, hlam]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
                                · linarith only [h179, h210, hlam]
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h212 | h212
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h213 | h213
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                                      · linarith only [h185, h189, h191, h209, h210, h214, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                                      · linarith only [h191, h209, h214, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                    · linarith only [h183, h213, hlam]
                                  · linarith only [h191, h209, h212, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo3]
                              · linarith only [h209, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
                            · linarith only [h177, h221, hlam]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                                · linarith only [h179, h224, hlam]
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h226 | h226
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h227 | h227
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                                      · linarith only [h190, h220, h221, h228, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h230 | h230
                                        · linarith only [h220, h221, h230, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                        · linarith only [h220, h221, h226, h230, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                    · linarith only [h183, h227, hlam]
                                  · linarith only [h226, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                              · linarith only [h220, h223, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo2]
                          · linarith only [h189, h190, h220, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h237 | h237
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
                          · linarith only [h177, h189, h238, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                            · linarith only [h177, h240, hlam]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                                · linarith only [h179, h243, hlam]
                                · linarith only [h189, h237, h238, h242, h243, hc23, hlam, hphi, ht12, u1ehi4]
                              · linarith only [h242, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
                          · linarith only [h185, h189, h247, hlam]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h249 | h249
                            · linarith only [h177, h249, hlam]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h252 | h252
                                · linarith only [h179, h252, hlam]
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                                      · linarith only [h186, h237, h247, h251, h256, hc23, hlam, hphi, ht12, u1ehi4]
                                      · linarith only [h185, h189, h251, h256, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                    · linarith only [h183, h255, hlam]
                                  · linarith only [h247, h251, h254, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo3]
                              · linarith only [h251, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                    · linarith only [h188, hc15, hlam, hphi, p0_1, u1ehi3]
                  · linarith only [h187, hlam, p0_0]
                · linarith only [h186, hc13, hlam, hphi, p0_1, u1ehi3]
              · linarith only [h185, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h176, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h267 | h267
    · rcases p0_3 (m.d 1 2) (by simp) with h268 | h268
      · linarith only [h268, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h270 | h270
        · linarith only [h270, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h272 | h272
          · linarith only [h272, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h274 | h274
            · linarith only [h274, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h276 | h276
              · rcases m.htr 0 1 3 (by decide) (by decide) with h277 | h277
                · rcases m.htr 0 1 4 (by decide) (by decide) with h278 | h278
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h279 | h279
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h280 | h280
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h281 | h281
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h282 | h282
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h283 | h283
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h284 | h284
                              · linarith only [h268, h284, hlam]
                              · linarith only [h282, h284, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo2]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
                              · linarith only [h268, h287, hlam]
                              · linarith only [h282, h287, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo2]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h290 | h290
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h291 | h291
                              · linarith only [h268, h291, hlam]
                              · linarith only [h290, h291, hc24, hlam, hphi, ht45, u5elo2]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                              · linarith only [h268, h294, hlam]
                              · linarith only [h294, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h297 | h297
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h299 | h299
                              · linarith only [h268, h299, hlam]
                              · linarith only [h297, h299, hc23, hlam, hphi, ht34, ht45, u5elo2]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
                              · linarith only [h268, h302, hlam]
                              · linarith only [h297, h302, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo2]
                          · linarith only [h280, h281, h297, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h306 | h306
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
                          · linarith only [h268, h280, h307, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h309 | h309
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h310 | h310
                              · linarith only [h268, h310, hlam]
                              · linarith only [h309, h310, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo2]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h313 | h313
                              · linarith only [h268, h313, hlam]
                              · linarith only [h313, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
                          · linarith only [h276, h280, h316, hlam]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h319 | h319
                              · linarith only [h268, h319, hlam]
                              · linarith only [h318, h319, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo2]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h322 | h322
                              · linarith only [h268, h322, hlam]
                              · linarith only [h322, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                    · linarith only [h279, hlam, p0_0]
                  · linarith only [h278, hc14, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h277, hc13, hlam, hphi, p0_1, u1ehi4]
              · linarith only [h276, hc12, hlam, hphi, p0_1, u1ehi4]
    · linarith only [h267, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi2, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_I_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h16, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                        · linarith only [h16, h9, hlam]
                      · linarith only [h15, h7, hlam]
                    · linarith only [h14, h5, hlam]
                  · linarith only [h13, hc14, hlam, hphi, p0_1, u1ehi1]
                · linarith only [h12, hc13, hlam, hphi, p0_1, u1ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                    · linarith only [h26, h37, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                        · linarith only [h37, h40, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h42 | h42
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h43 | h43
                            · linarith only [h43, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                            · linarith only [h32, h43, hlam]
                          · linarith only [h30, h42, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                        · linarith only [h37, h47, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                            · linarith only [h50, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                            · linarith only [h32, h50, hlam]
                          · linarith only [h30, h49, hlam]
                  · linarith only [h36, hc14, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h35, hlam, p0_0]
              · linarith only [h34, hc12, hlam, hphi, p0_1, u1ehi2]
    · linarith only [h25, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h58 | h58
    · rcases p0_3 (m.d 1 2) (by simp) with h59 | h59
      · linarith only [h59, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h61 | h61
        · linarith only [h61, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h63 | h63
          · linarith only [h63, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h65 | h65
            · linarith only [h65, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h67 | h67
              · rcases m.htr 0 1 3 (by decide) (by decide) with h68 | h68
                · rcases m.htr 0 1 4 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                      · linarith only [h59, h71, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                        · linarith only [h71, h73, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                          · linarith only [h61, h75, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                            · linarith only [h70, h71, h77, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                              · linarith only [h79, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                              · linarith only [h65, h79, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                      · linarith only [h59, h82, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                        · linarith only [h82, h84, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                          · linarith only [h61, h86, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                            · linarith only [h86, h88, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                              · linarith only [h90, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                              · linarith only [h65, h90, hlam]
                  · linarith only [h69, hlam, p0_0]
                · linarith only [h68, hc13, hlam, hphi, p0_1, u1ehi3]
              · linarith only [h67, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h58, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h97 | h97
    · rcases p0_3 (m.d 1 2) (by simp) with h98 | h98
      · linarith only [h98, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h100 | h100
        · linarith only [h100, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
          · linarith only [h102, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h104 | h104
            · linarith only [h104, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
              · rcases m.htr 0 1 3 (by decide) (by decide) with h107 | h107
                · rcases m.htr 0 1 4 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                        · linarith only [h111, h98, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                            · linarith only [h100, h114, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                              · linarith only [h102, h116, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                                · linarith only [h109, h111, h118, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                · linarith only [h109, h111, h113, h118, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                            · linarith only [h100, h121, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                              · linarith only [h102, h123, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                                · linarith only [h113, h125, hc23, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h127 | h127
                                  · linarith only [h110, h111, h125, h127, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                                    · linarith only [h113, h123, h129, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                    · linarith only [h113, h129, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                        · linarith only [h132, h98, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                          · linarith only [h109, h110, h134, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                            · linarith only [h100, h136, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                              · linarith only [h102, h138, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                                · linarith only [h134, h140, hc23, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                                  · linarith only [h109, h110, h138, h142, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                                    · linarith only [h109, h110, h138, h144, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                    · linarith only [h134, h144, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h147 | h147
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
                        · linarith only [h148, h98, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                            · linarith only [h100, h151, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                              · linarith only [h102, h153, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                                  · linarith only [h109, h147, h151, h156, hc23, hlam, hphi, ht12, u1ehi3]
                                  · linarith only [h109, h147, h156, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                · linarith only [h109, h147, h155, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h109, h147, h150, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                        · linarith only [h161, h98, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
                            · linarith only [h100, h164, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h166 | h166
                              · linarith only [h102, h166, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h169 | h169
                                  · linarith only [h164, h169, hc23, hlam, hphi, ht12, u1ehi2]
                                  · linarith only [h109, h169, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h109, h163, h168, hc13, hlam, hphi, u1ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                            · linarith only [h100, h173, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                              · linarith only [h102, h175, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                                · linarith only [h109, h163, h177, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h109, h177, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h108, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
                · linarith only [h107, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
              · linarith only [h102, h106, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h97, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_I_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
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
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h0, h14, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht01, u1elo2]
        · linarith only [h0, h17, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h12, h21, hlam, ht01, u1elo1]
        · linarith only [h0, h21, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h12, h24, hlam, ht01, u1elo1]
        · linarith only [h0, h24, hlam, ht01, u1elo3]
  · linarith only [h0, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]

theorem n7l_sAA5_H_I_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h0, h14, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht01, u1elo2]
        · linarith only [h0, h17, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h12, h21, hlam, ht01, u1elo1]
        · linarith only [h0, h21, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h12, h24, hlam, ht01, u1elo1]
        · linarith only [h0, h24, hlam, ht01, u1elo3]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h27 | h27
    · rcases m.htr 0 1 3 (by decide) (by decide) with h28 | h28
      · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
        · rcases m.htr 0 1 5 (by decide) (by decide) with h30 | h30
          · linarith only [h0, h30, hlam, ht01, u1elo0]
          · linarith only [h0, h30, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h33 | h33
          · linarith only [h0, h29, h33, hlam, ht01, u1elo3]
          · linarith only [h0, h33, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h36 | h36
        · rcases m.htr 0 1 5 (by decide) (by decide) with h37 | h37
          · linarith only [h0, h28, h37, hlam, ht01, u1elo2]
          · linarith only [h0, h37, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
          · linarith only [h0, h28, h40, hlam, ht01, u1elo2]
          · linarith only [h0, h40, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h43 | h43
      · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
          · linarith only [h0, h27, h45, hlam, ht01, u1elo1]
          · linarith only [h0, h45, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h48 | h48
          · linarith only [h0, h27, h48, hlam, ht01, u1elo1]
          · linarith only [h0, h48, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h51 | h51
        · rcases m.htr 0 1 5 (by decide) (by decide) with h52 | h52
          · linarith only [h0, h27, h52, hlam, ht01, u1elo1]
          · linarith only [h0, h52, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h55 | h55
          · linarith only [h0, h27, h55, hlam, ht01, u1elo1]
          · linarith only [h0, h55, hlam, ht01, u1elo4]

theorem n7l_sAA5_H_I_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
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
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h0, h14, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht01, u1elo2]
        · linarith only [h0, h17, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h12, h21, hlam, ht01, u1elo1]
        · linarith only [h0, h21, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h12, h24, hlam, ht01, u1elo1]
        · linarith only [h0, h24, hlam, ht01, u1elo3]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h27 | h27
    · rcases m.htr 0 1 3 (by decide) (by decide) with h28 | h28
      · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
        · rcases m.htr 0 1 5 (by decide) (by decide) with h30 | h30
          · linarith only [h0, h30, hlam, ht01, u1elo0]
          · linarith only [h0, h30, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h33 | h33
          · linarith only [h29, h33, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
          · linarith only [h0, h33, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h36 | h36
        · rcases m.htr 0 1 5 (by decide) (by decide) with h37 | h37
          · linarith only [h28, h37, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
          · linarith only [h0, h37, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
          · linarith only [h28, h40, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
          · linarith only [h0, h40, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h43 | h43
      · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
          · linarith only [h27, h45, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
          · linarith only [h0, h45, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h48 | h48
          · linarith only [h27, h48, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
          · linarith only [h0, h48, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h51 | h51
        · rcases m.htr 0 1 5 (by decide) (by decide) with h52 | h52
          · linarith only [h27, h52, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
          · linarith only [h0, h52, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h55 | h55
          · linarith only [h27, h55, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
          · linarith only [h0, h55, hlam, ht01, u1elo4]

theorem n7l_sAA5_H_L_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_L_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_L_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h28 | h28
    · linarith only [h28, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h28, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_L_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · linarith only [h1, h3, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
            · linarith only [h1, h3, h7, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
              · linarith only [h1, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                · linarith only [h11, h2, h9, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                          · linarith only [h13, h15, h18, h3, h9, hc12, hc23, hlam, hphi]
                          · linarith only [h17, h18, h3, h9, hc12, hc24, hlam, hphi]
                        · linarith only [h17, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h16, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h11, h15, h23, hc13, hc34, hlam, hphi]
                      · linarith only [h23, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · linarith only [h2, hc01, hlam, hphi, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA5_H_L_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                    · linarith only [h1, h10, h8, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                      · linarith only [h1, h12, h8, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h12, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
                    · linarith only [h1, h15, h17, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h1, h15, h19, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h19, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
                · linarith only [h22, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h24, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                    · linarith only [h1, h24, h26, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                      · linarith only [h1, h24, h28, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h28, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h31 | h31
              · rcases m.htr 0 4 5 (by decide) (by decide) with h32 | h32
                · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                  · linarith only [h0, h33, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                    · linarith only [h1, h33, h35, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                      · linarith only [h1, h33, h37, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h37, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h31, h32, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                  · linarith only [h0, h42, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                    · linarith only [h1, h42, h44, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                      · linarith only [h1, h42, h46, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h4, h46, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                  · linarith only [h0, h49, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                    · linarith only [h1, h49, h51, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                      · linarith only [h1, h49, h53, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h4, h53, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
            · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
              · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
                · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                  · linarith only [h0, h59, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h61 | h61
                    · linarith only [h1, h59, h61, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                      · linarith only [h1, h4, h59, h63, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                        · linarith only [h1, h65, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h56, h59, h65, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                  · linarith only [h0, h68, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
                    · linarith only [h1, h68, h70, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
                      · linarith only [h0, h4, h72, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
                        · linarith only [h1, h74, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h1, h56, h68, h74, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
                · linarith only [h56, h57, h77, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                  · linarith only [h0, h79, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                    · linarith only [h1, h79, h81, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                      · linarith only [h0, h4, h83, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                        · linarith only [h1, h85, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h3, h56, h57, h79, h85, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h88 | h88
              · rcases m.htr 0 4 5 (by decide) (by decide) with h89 | h89
                · rcases m.htr 1 2 3 (by decide) (by decide) with h90 | h90
                  · linarith only [h0, h90, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                    · linarith only [h1, h90, h92, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
                      · linarith only [h0, h4, h94, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                        · linarith only [h1, h56, h96, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                          · linarith only [h2, h96, h98, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h56, h88, h90, h98, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h56, h88, h89, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
                · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                  · linarith only [h0, h103, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
                    · linarith only [h1, h103, h105, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                      · linarith only [h0, h107, h4, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
                        · linarith only [h1, h109, h56, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
                          · linarith only [h1, h111, h88, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                            · linarith only [h113, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h102, h103, h109, h113, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                  · linarith only [h0, h116, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                    · linarith only [h0, h118, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
                      · linarith only [h0, h120, h4, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h122 | h122
                        · linarith only [h1, h122, h56, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                          · linarith only [h1, h124, h88, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
                            · linarith only [h102, h126, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                                    · linarith only [h102, h116, h122, h128, h131, h2, hc12, hc23, hlam, hphi]
                                    · linarith only [h1, h116, h130, h131, h56, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                                    · linarith only [h102, h116, h122, h128, h134, h2, hc12, hc23, hlam, hphi]
                                    · rcases h5bigk with h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [hlam, p136_0]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h116, h122, h126, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p136_1, u1elo0]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h4, hlam, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h88, hlam, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h102, hlam, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h3, hlam, p136_0]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [hlam, p136_0]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h120, hlam, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h124, hlam, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h126, hlam, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        rcases p136_3 (m.d 0 5) (by simp) with h147 | h147
                                        · linarith only [h147, h4, hlam]
                                        · rcases p136_3 (m.d 1 5) (by simp) with h149 | h149
                                          · linarith only [h120, h149, hlam]
                                          · rcases p136_3 (m.d 2 5) (by simp) with h151 | h151
                                            · rcases p136_3 (m.d 3 5) (by simp) with h152 | h152
                                              · linarith only [h129, h152, hlam]
                                              · linarith only [h152, h88, hlam]
                                            · linarith only [h151, h4, hlam]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        rcases p136_3 (m.d 0 5) (by simp) with h156 | h156
                                        · linarith only [h156, h4, hlam]
                                        · linarith only [h156, h3, hlam]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [hlam, p136_0]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h1, h116, h130, h134, h56, hc12, hc45, hlam, hphi, ht23, ht34, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h130, hlam, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h116, h122, h126, h129, h3, hc12, hc23, hlam, hphi, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h116, h122, h126, h129, hc12, hc23, hlam, hphi, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h129, hlam, p136_0]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [hlam, p136_0]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h134, hlam, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        rcases p136_3 (m.d 0 5) (by simp) with h167 | h167
                                        · linarith only [h102, h167, hlam]
                                        · rcases p136_3 (m.d 1 5) (by simp) with h169 | h169
                                          · linarith only [h126, h169, hlam]
                                          · rcases p136_3 (m.d 2 5) (by simp) with h171 | h171
                                            · linarith only [h130, h171, hlam]
                                            · linarith only [h171, h4, hlam]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        rcases p136_3 (m.d 0 5) (by simp) with h174 | h174
                                        · linarith only [h102, h174, hlam]
                                        · linarith only [h174, h3, hlam]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [h1, h116, h88, hc12, hc45, hlam, hphi, ht23, ht34, p136_1]
                                      · obtain ⟨p136_0, p136_1, p136_2, p136_3⟩ := h136c
                                        linarith only [hlam, p136_0]
                                · linarith only [h1, h116, h128, h129, h56, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h181 | h181
                                · linarith only [h1, h116, h128, h181, h88, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h183 | h183
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h184 | h184
                                    · rcases h5bigk with h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [hlam, p185_0]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h116, h122, h126, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p185_1, u0elo4]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h4, hlam, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h88, hlam, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h102, hlam, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h3, hlam, p185_0]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [hlam, p185_0]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h120, hlam, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h124, hlam, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h126, hlam, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        rcases p185_3 (m.d 0 5) (by simp) with h196 | h196
                                        · linarith only [h196, h4, hlam]
                                        · rcases p185_3 (m.d 1 5) (by simp) with h198 | h198
                                          · linarith only [h120, h198, hlam]
                                          · rcases p185_3 (m.d 2 5) (by simp) with h200 | h200
                                            · rcases p185_3 (m.d 3 5) (by simp) with h201 | h201
                                              · rcases p185_3 (m.d 4 5) (by simp) with h202 | h202
                                                · linarith only [h183, h202, hlam]
                                                · linarith only [h102, h202, hlam]
                                              · linarith only [h201, h88, hlam]
                                            · linarith only [h200, h4, hlam]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        rcases p185_3 (m.d 0 5) (by simp) with h207 | h207
                                        · linarith only [h207, h4, hlam]
                                        · linarith only [h207, h3, hlam]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [hlam, p185_0]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h181, hlam, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h102, h116, h122, h183, h2, hc12, hc24, hlam, hphi, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        rcases p185_3 (m.d 0 5) (by simp) with h213 | h213
                                        · linarith only [h213, h88, hlam]
                                        · rcases p185_3 (m.d 1 5) (by simp) with h215 | h215
                                          · linarith only [h124, h215, hlam]
                                          · rcases p185_3 (m.d 2 5) (by simp) with h217 | h217
                                            · linarith only [h181, h217, hlam]
                                            · linarith only [h217, h4, hlam]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        rcases p185_3 (m.d 0 5) (by simp) with h220 | h220
                                        · linarith only [h220, h88, hlam]
                                        · linarith only [h220, h3, hlam]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h0, h184, h4, hc12, hc34, hlam, hphi, ht23, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [hlam, p185_0]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h102, h116, h122, h184, h2, hc12, hc34, hlam, hphi, ht23, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h116, h122, h126, h128, h183, h3, hc12, hc34, hlam, hphi, ht23, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h116, h122, h126, h128, h183, hc12, hc34, hlam, hphi, ht23, p185_1]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h183, hlam, p185_0]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [h184, hlam, p185_0]
                                      · obtain ⟨p185_0, p185_1, p185_2, p185_3⟩ := h185c
                                        linarith only [hlam, p185_0]
                                    · linarith only [h128, h183, h184, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
                                    · linarith only [h116, h128, h183, h232, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h116, h128, h232, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h3, hc01, hlam, hphi, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA5_H_L_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_L_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_L_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h28 | h28
    · linarith only [h28, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h28, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_R_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
                · linarith only [h16, h5, hlam]
                · linarith only [h16, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h15, hlam, p0_0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 1 5) (by simp) with h22 | h22
            · rcases m.htr 0 1 2 (by decide) (by decide) with h23 | h23
              · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 0 1 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h21, h25, hlam]
                  · linarith only [h25, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h24, h5, hlam, p0_1]
              · linarith only [h23, hlam, p0_0]
            · linarith only [h22, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h31 | h31
            · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h31, h35, hlam]
                    · linarith only [h35, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h21, h34, hlam, p0_1]
                · linarith only [h33, h5, hlam, p0_1]
              · linarith only [h32, hlam, p0_0]
            · linarith only [h31, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · rcases p0_3 (m.d 1 2) (by simp) with h44 | h44
      · rcases p0_3 (m.d 1 3) (by simp) with h45 | h45
        · linarith only [h45, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h47 | h47
          · rcases p0_3 (m.d 1 5) (by simp) with h48 | h48
            · rcases m.htr 0 1 2 (by decide) (by decide) with h49 | h49
              · linarith only [h44, h49, hlam]
              · linarith only [h49, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h48, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h44, h54, hlam]
              · linarith only [h54, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h53, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h58 | h58
        · linarith only [h58, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 1 5) (by simp) with h61 | h61
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · rcases m.htr 0 1 3 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
                  · linarith only [h60, h64, hlam]
                  · linarith only [h44, h64, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h63, hlam, p0_0]
              · linarith only [h44, h62, hlam, p0_1]
            · linarith only [h61, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h70 | h70
            · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
              · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h70, h74, hlam]
                    · linarith only [h74, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h60, h73, hlam, p0_1]
                · linarith only [h72, hlam, p0_0]
              · linarith only [h44, h71, hlam, p0_1]
            · linarith only [h70, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
    · linarith only [h43, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h82 | h82
    · rcases p0_3 (m.d 1 2) (by simp) with h83 | h83
      · rcases p0_3 (m.d 1 3) (by simp) with h84 | h84
        · rcases p0_3 (m.d 1 4) (by simp) with h85 | h85
          · linarith only [h85, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h87 | h87
            · rcases m.htr 0 1 2 (by decide) (by decide) with h88 | h88
              · linarith only [h83, h88, hlam]
              · linarith only [h88, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h87, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
          · linarith only [h92, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h94 | h94
            · rcases m.htr 0 1 2 (by decide) (by decide) with h95 | h95
              · linarith only [h83, h95, hlam]
              · linarith only [h84, h95, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h94, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h99 | h99
        · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
          · linarith only [h100, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h102 | h102
            · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
              · rcases m.htr 0 1 3 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h99, hlam]
                · linarith only [h104, h83, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h103, h83, hlam, p0_1]
            · linarith only [h102, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h109 | h109
          · linarith only [h109, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h111 | h111
            · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 1 3 (by decide) (by decide) with h113 | h113
                · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h111, h115, hlam]
                    · linarith only [h115, h99, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h114, hlam, p0_0]
                · linarith only [h113, h83, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h83, hlam, p0_1]
            · linarith only [h111, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
    · linarith only [h82, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h126 | h126
    · rcases p0_3 (m.d 1 2) (by simp) with h127 | h127
      · rcases p0_3 (m.d 1 3) (by simp) with h128 | h128
        · linarith only [h128, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h130 | h130
          · rcases p0_3 (m.d 1 5) (by simp) with h131 | h131
            · rcases m.htr 0 1 2 (by decide) (by decide) with h132 | h132
              · linarith only [h132, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h126, h132, hlam]
            · linarith only [h131, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h136 | h136
            · rcases m.htr 0 1 2 (by decide) (by decide) with h137 | h137
              · linarith only [h137, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h126, h137, hlam]
            · linarith only [h136, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
      · linarith only [h127, hlam, p0_0]
    · linarith only [h126, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h143 | h143
    · rcases p0_3 (m.d 1 2) (by simp) with h144 | h144
      · rcases p0_3 (m.d 1 3) (by simp) with h145 | h145
        · rcases p0_3 (m.d 1 4) (by simp) with h146 | h146
          · linarith only [h146, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h148 | h148
            · rcases m.htr 0 1 2 (by decide) (by decide) with h149 | h149
              · linarith only [h149, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h143, h149, hlam]
            · linarith only [h148, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h153 | h153
          · linarith only [h153, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h155 | h155
            · rcases m.htr 0 1 2 (by decide) (by decide) with h156 | h156
              · linarith only [h145, h156, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h143, h156, hlam]
            · linarith only [h155, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
      · linarith only [h144, hlam, p0_0]
    · linarith only [h143, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h164 | h164
    · rcases p0_3 (m.d 1 2) (by simp) with h165 | h165
      · linarith only [h165, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h167 | h167
        · rcases p0_3 (m.d 1 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 1 5) (by simp) with h169 | h169
            · rcases m.htr 0 1 2 (by decide) (by decide) with h170 | h170
              · rcases m.htr 0 1 3 (by decide) (by decide) with h171 | h171
                · linarith only [h171, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h164, h171, hlam]
              · linarith only [h170, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h164, h169, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h176 | h176
            · rcases m.htr 0 1 2 (by decide) (by decide) with h177 | h177
              · rcases m.htr 0 1 3 (by decide) (by decide) with h178 | h178
                · linarith only [h178, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h164, h178, hlam]
              · linarith only [h177, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h176, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
        · linarith only [h167, hlam, p0_0]
    · linarith only [h164, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h186 | h186
    · rcases p0_3 (m.d 1 2) (by simp) with h187 | h187
      · rcases p0_3 (m.d 1 3) (by simp) with h188 | h188
        · rcases p0_3 (m.d 1 4) (by simp) with h189 | h189
          · linarith only [h189, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h191 | h191
            · rcases m.htr 0 1 2 (by decide) (by decide) with h192 | h192
              · linarith only [h187, h192, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h192, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h186, h191, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
        · linarith only [h188, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h197 | h197
        · rcases p0_3 (m.d 1 4) (by simp) with h198 | h198
          · linarith only [h198, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h200 | h200
            · rcases m.htr 0 1 2 (by decide) (by decide) with h201 | h201
              · rcases m.htr 0 1 3 (by decide) (by decide) with h202 | h202
                · linarith only [h187, h202, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h186, h202, hlam]
              · linarith only [h187, h201, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h200, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
        · linarith only [h197, hlam, p0_0]
    · linarith only [h186, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h211 | h211
    · rcases p0_3 (m.d 1 2) (by simp) with h212 | h212
      · linarith only [h212, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h214 | h214
        · rcases p0_3 (m.d 1 4) (by simp) with h215 | h215
          · rcases p0_3 (m.d 1 5) (by simp) with h216 | h216
            · rcases m.htr 0 1 2 (by decide) (by decide) with h217 | h217
              · rcases m.htr 0 1 3 (by decide) (by decide) with h218 | h218
                · linarith only [h214, h218, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h218, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h211, h217, hlam, p0_1]
            · linarith only [h214, h216, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
          · linarith only [h215, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h224 | h224
          · rcases p0_3 (m.d 1 5) (by simp) with h225 | h225
            · rcases m.htr 0 1 2 (by decide) (by decide) with h226 | h226
              · rcases m.htr 0 1 3 (by decide) (by decide) with h227 | h227
                · rcases m.htr 0 1 4 (by decide) (by decide) with h228 | h228
                  · linarith only [h228, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h211, h228, hlam]
                · linarith only [h214, h227, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h211, h226, hlam, p0_1]
            · linarith only [h225, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
          · linarith only [h224, hlam, p0_0]
    · linarith only [h211, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h236 | h236
    · rcases p0_3 (m.d 1 2) (by simp) with h237 | h237
      · rcases p0_3 (m.d 1 3) (by simp) with h238 | h238
        · linarith only [h238, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h240 | h240
          · rcases p0_3 (m.d 1 5) (by simp) with h241 | h241
            · rcases m.htr 0 1 2 (by decide) (by decide) with h242 | h242
              · linarith only [h237, h242, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h242, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h236, h241, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
          · linarith only [h240, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h247 | h247
        · linarith only [h247, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h249 | h249
          · rcases p0_3 (m.d 1 5) (by simp) with h250 | h250
            · rcases m.htr 0 1 2 (by decide) (by decide) with h251 | h251
              · rcases m.htr 0 1 3 (by decide) (by decide) with h252 | h252
                · rcases m.htr 0 1 4 (by decide) (by decide) with h253 | h253
                  · linarith only [h237, h253, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h236, h253, hlam]
                · linarith only [h252, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h236, h251, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h236, h250, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
          · linarith only [h249, hlam, p0_0]
    · linarith only [h236, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h264 | h264
    · rcases p0_3 (m.d 1 2) (by simp) with h265 | h265
      · linarith only [h265, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h267 | h267
        · rcases p0_3 (m.d 1 4) (by simp) with h268 | h268
          · rcases p0_3 (m.d 1 5) (by simp) with h269 | h269
            · rcases m.htr 0 1 2 (by decide) (by decide) with h270 | h270
              · rcases m.htr 0 1 3 (by decide) (by decide) with h271 | h271
                · linarith only [h267, h271, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h271, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h264, h270, hlam, p0_1]
            · linarith only [h269, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h276 | h276
            · rcases m.htr 0 1 2 (by decide) (by decide) with h277 | h277
              · rcases m.htr 0 1 3 (by decide) (by decide) with h278 | h278
                · linarith only [h267, h278, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h278, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h264, h277, hlam, p0_1]
            · linarith only [h276, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h283 | h283
          · rcases p0_3 (m.d 1 5) (by simp) with h284 | h284
            · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
              · rcases m.htr 0 1 3 (by decide) (by decide) with h286 | h286
                · rcases m.htr 0 1 4 (by decide) (by decide) with h287 | h287
                  · linarith only [h283, h287, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h287, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h264, h267, h286, hlam, p0_1]
              · linarith only [h264, h285, hlam, p0_1]
            · linarith only [h284, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h293 | h293
            · rcases m.htr 0 1 2 (by decide) (by decide) with h294 | h294
              · rcases m.htr 0 1 3 (by decide) (by decide) with h295 | h295
                · rcases m.htr 0 1 4 (by decide) (by decide) with h296 | h296
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h297 | h297
                    · linarith only [h297, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h264, h297, hlam]
                  · linarith only [h283, h296, hc01, hc15, hlam, hphi, p0_1]
                · linarith only [h264, h267, h295, hlam, p0_1]
              · linarith only [h264, h294, hlam, p0_1]
            · linarith only [h293, hlam, p0_0]
    · linarith only [h264, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h305 | h305
    · rcases p0_3 (m.d 1 2) (by simp) with h306 | h306
      · rcases p0_3 (m.d 1 3) (by simp) with h307 | h307
        · linarith only [h307, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h309 | h309
          · rcases p0_3 (m.d 1 5) (by simp) with h310 | h310
            · rcases m.htr 0 1 2 (by decide) (by decide) with h311 | h311
              · linarith only [h306, h311, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h311, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h310, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h315 | h315
            · rcases m.htr 0 1 2 (by decide) (by decide) with h316 | h316
              · linarith only [h306, h316, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h316, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h315, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h320 | h320
        · linarith only [h320, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h322 | h322
          · rcases p0_3 (m.d 1 5) (by simp) with h323 | h323
            · rcases m.htr 0 1 2 (by decide) (by decide) with h324 | h324
              · rcases m.htr 0 1 3 (by decide) (by decide) with h325 | h325
                · rcases m.htr 0 1 4 (by decide) (by decide) with h326 | h326
                  · linarith only [h306, h322, h326, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h326, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h305, h325, hlam, p0_1]
              · linarith only [h305, h306, h324, hlam, p0_1]
            · linarith only [h323, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h332 | h332
            · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
              · rcases m.htr 0 1 3 (by decide) (by decide) with h334 | h334
                · rcases m.htr 0 1 4 (by decide) (by decide) with h335 | h335
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h336 | h336
                    · linarith only [h306, h336, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h305, h336, hlam]
                  · linarith only [h322, h335, hc01, hc15, hlam, hphi, p0_1]
                · linarith only [h305, h334, hlam, p0_1]
              · linarith only [h305, h306, h333, hlam, p0_1]
            · linarith only [h332, hlam, p0_0]
    · linarith only [h305, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h344 | h344
    · rcases p0_3 (m.d 1 2) (by simp) with h345 | h345
      · rcases p0_3 (m.d 1 3) (by simp) with h346 | h346
        · rcases p0_3 (m.d 1 4) (by simp) with h347 | h347
          · linarith only [h347, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h349 | h349
            · rcases m.htr 0 1 2 (by decide) (by decide) with h350 | h350
              · linarith only [h345, h350, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h350, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h349, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h354 | h354
          · linarith only [h354, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h356 | h356
            · rcases m.htr 0 1 2 (by decide) (by decide) with h357 | h357
              · linarith only [h345, h346, h357, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h357, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h356, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h361 | h361
        · rcases p0_3 (m.d 1 4) (by simp) with h362 | h362
          · linarith only [h362, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h364 | h364
            · rcases m.htr 0 1 2 (by decide) (by decide) with h365 | h365
              · rcases m.htr 0 1 3 (by decide) (by decide) with h366 | h366
                · linarith only [h345, h361, h366, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h366, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h344, h345, h365, hlam, p0_1]
            · linarith only [h364, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h371 | h371
          · linarith only [h371, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h373 | h373
            · rcases m.htr 0 1 2 (by decide) (by decide) with h374 | h374
              · rcases m.htr 0 1 3 (by decide) (by decide) with h375 | h375
                · rcases m.htr 0 1 4 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h377 | h377
                    · linarith only [h345, h377, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h344, h377, hlam]
                  · linarith only [h376, hc01, hc15, hlam, hphi, p0_1]
                · linarith only [h344, h361, h375, hlam, p0_1]
              · linarith only [h344, h345, h374, hlam, p0_1]
            · linarith only [h373, hlam, p0_0]
    · linarith only [h344, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_R_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h1ehi := hb1.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h11, h14, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h11, h13, h14, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h11, h13, h17, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
                              · rcases h5bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h2, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p19_1, u1ehi4]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h22 | h22
                                  · rcases p19_3 (m.d 1 5) (by simp) with h23 | h23
                                    · linarith only [h1, h23, hlam]
                                    · linarith only [h23, h7, hlam]
                                  · linarith only [h22, h3, hlam]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h27 | h27
                                  · rcases p19_3 (m.d 1 5) (by simp) with h28 | h28
                                    · linarith only [h1, h28, hlam]
                                    · linarith only [h28, h9, hlam]
                                  · linarith only [h27, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h32 | h32
                                  · rcases p19_3 (m.d 1 5) (by simp) with h33 | h33
                                    · linarith only [h1, h33, hlam]
                                    · linarith only [h10, h33, hlam]
                                  · linarith only [h32, h5, hlam]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h1, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h39 | h39
                                  · rcases p19_3 (m.d 1 5) (by simp) with h40 | h40
                                    · rcases p19_3 (m.d 2 5) (by simp) with h41 | h41
                                      · linarith only [h41, h7, hlam]
                                      · rcases p19_3 (m.d 3 5) (by simp) with h43 | h43
                                        · linarith only [h43, h9, hlam]
                                        · rcases p19_3 (m.d 4 5) (by simp) with h45 | h45
                                          · linarith only [h10, h45, hlam]
                                          · linarith only [h13, h45, hlam]
                                    · linarith only [h40, h7, hlam]
                                  · linarith only [h3, h39, hlam]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h50 | h50
                                  · rcases p19_3 (m.d 1 5) (by simp) with h51 | h51
                                    · rcases p19_3 (m.d 2 5) (by simp) with h52 | h52
                                      · linarith only [h52, h7, hlam]
                                      · linarith only [h12, h52, hlam]
                                    · linarith only [h51, h9, hlam]
                                  · linarith only [h0, h12, h3, h50, hc01, hlam, hphi, u0ehi4]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h10, h13, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h3, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h7, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h12, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h13, hlam, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p19_1, u0ehi4]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h9, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h12, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h17, hlam, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h5, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h10, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h10, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h10, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                          · linarith only [h0, h11, h12, h6, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
                          · linarith only [h0, h11, h6, h74, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                              · rcases h5bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi4]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h81 | h81
                                  · rcases p78_3 (m.d 1 5) (by simp) with h82 | h82
                                    · linarith only [h1, h82, hlam]
                                    · linarith only [h7, h82, hlam]
                                  · linarith only [h3, h81, hlam]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h86 | h86
                                  · rcases p78_3 (m.d 1 5) (by simp) with h87 | h87
                                    · linarith only [h1, h87, hlam]
                                    · linarith only [h87, h9, hlam]
                                  · linarith only [h86, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h91 | h91
                                  · rcases p78_3 (m.d 1 5) (by simp) with h92 | h92
                                    · linarith only [h1, h92, hlam]
                                    · linarith only [h10, h92, hlam]
                                  · linarith only [h5, h91, hlam]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h1, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h98 | h98
                                  · rcases p78_3 (m.d 1 5) (by simp) with h99 | h99
                                    · rcases p78_3 (m.d 2 5) (by simp) with h100 | h100
                                      · linarith only [h100, h7, hlam]
                                      · rcases p78_3 (m.d 3 5) (by simp) with h102 | h102
                                        · linarith only [h102, h9, hlam]
                                        · linarith only [h102, h74, hlam]
                                    · linarith only [h7, h99, hlam]
                                  · linarith only [h3, h98, hlam]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h0, h10, h6, h74, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h108 | h108
                                  · rcases p78_3 (m.d 1 5) (by simp) with h109 | h109
                                    · rcases p78_3 (m.d 2 5) (by simp) with h110 | h110
                                      · linarith only [h110, h7, hlam]
                                      · linarith only [h110, h76, hlam]
                                    · linarith only [h10, h109, hlam]
                                  · linarith only [h108, h5, hlam]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h3, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h7, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h74, hlam, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h0, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h0, h6, h77, h8, hc01, hc05, hlam, hphi, ht0b, ht5b, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h9, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h0, h6, h77, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h0, h6, h77, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h5, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h10, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h76, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h77, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                              · linarith only [h0, h10, h11, h6, h77, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                              · linarith only [h0, h11, h131, h6, h76, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h0, h10, h11, h131, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h10, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                    · linarith only [h9, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                  · linarith only [h8, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                · linarith only [h7, hc25, hlam, hphi, ht12, u1ehi1]
              · linarith only [h6, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc25, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc15, hlam, hphi, u1ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sAA5_H_R_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc13, hlam, hphi, p0_1, u1ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · linarith only [h7, hc14, hlam, hphi, p0_1, u1ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h9 | h9
            · linarith only [h9, hc15, hlam, hphi, p0_1, u1ehi1]
            · rcases h5bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h13 | h13
                · rcases p11_3 (m.d 1 5) (by simp) with h14 | h14
                  · linarith only [h14, hlam, p11_0]
                  · rcases p11_3 (m.d 2 5) (by simp) with h16 | h16
                    · linarith only [h16, hc25, hlam, hphi, ht12, p11_1, u1ehi4]
                    · rcases p11_3 (m.d 3 5) (by simp) with h18 | h18
                      · linarith only [h18, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi4]
                      · rcases p11_3 (m.d 4 5) (by simp) with h20 | h20
                        · linarith only [h20, hc45, hlam, hphi, ht12, ht23, ht34, p11_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h22 | h22
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h23 | h23
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h25 | h25
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h27 | h27
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                                                        · linarith only [h31, h37, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                        · linarith only [h31, h34, h37, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                                      · linarith only [h20, h36, hlam]
                                                    · linarith only [h18, h35, hlam]
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                                                        · linarith only [h31, h44, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                                                          · linarith only [h32, h44, h46, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                                          · linarith only [h34, h42, h46, hc23, hc34, hlam, hphi]
                                                      · linarith only [h20, h43, hlam]
                                                    · linarith only [h18, h42, hlam]
                                                · linarith only [h16, h33, hlam]
                                              · linarith only [h32, h7, hlam]
                                            · linarith only [h31, h5, hlam]
                                          · linarith only [h30, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                                        · linarith only [h22, h27, h29, hc01, hc35, hlam, hphi, ht12, ht23, p11_1, u0ehi2, u1ehi4]
                                      · linarith only [h22, h27, h28, hc01, hc34, hlam, hphi, ht12, ht23, p11_1, u0ehi2, u1ehi4]
                                    · linarith only [h27, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                                  · linarith only [h25, h26, hc01, hc23, hlam, hphi, ht12, p11_1, u0ehi1, u1ehi4]
                                · linarith only [h25, hlam, p11_0]
                              · linarith only [h24, h7, hc12, hlam, hphi, ht01, u0ehi0]
                            · linarith only [h23, h5, hlam, p0_1]
                          · linarith only [h22, hlam, p0_0]
                · linarith only [h13, hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h64 | h64
                · rcases p11_3 (m.d 1 5) (by simp) with h65 | h65
                  · linarith only [h65, h9, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p11_3 (m.d 2 5) (by simp) with h67 | h67
                    · linarith only [h67, hlam, p11_0]
                    · rcases p11_3 (m.d 3 5) (by simp) with h69 | h69
                      · linarith only [h65, h69, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi4]
                      · rcases p11_3 (m.d 4 5) (by simp) with h71 | h71
                        · linarith only [h65, h71, hc45, hlam, hphi, ht12, ht23, ht34, p11_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h73 | h73
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h74 | h74
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h75 | h75
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h76 | h76
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h77 | h77
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h78 | h78
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h79 | h79
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h80 | h80
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h81 | h81
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                                                · linarith only [h65, h84, hlam]
                                                · linarith only [h84, h9, hlam]
                                              · linarith only [h7, h83, hlam]
                                            · linarith only [h5, h82, hlam]
                                          · linarith only [h71, h81, hc05, hlam, hphi, p11_1, u0ehi3]
                                        · linarith only [h69, h73, h78, h79, h80, hc01, hlam, hphi, p11_1, u0ehi3]
                                      · linarith only [h79, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h78, hlam, p11_0]
                                  · linarith only [h65, h76, h77, hc01, hc23, hlam, hphi, ht12, p11_1, u0ehi1, u1ehi4]
                                · linarith only [h65, h76, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                              · linarith only [h75, hc14, hlam, hphi, p0_1, u1ehi1]
                            · linarith only [h74, hc13, hlam, hphi, p0_1, u1ehi1]
                          · linarith only [h73, hlam, p0_0]
                · linarith only [h64, hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h99 | h99
                · rcases p11_3 (m.d 1 5) (by simp) with h100 | h100
                  · linarith only [h100, h9, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p11_3 (m.d 2 5) (by simp) with h102 | h102
                    · linarith only [h100, h102, hc25, hlam, hphi, ht12, p11_1, u1ehi4]
                    · rcases p11_3 (m.d 3 5) (by simp) with h104 | h104
                      · linarith only [h104, hlam, p11_0]
                      · rcases p11_3 (m.d 4 5) (by simp) with h106 | h106
                        · linarith only [h100, h106, hc45, hlam, hphi, ht12, ht23, ht34, p11_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h108 | h108
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h109 | h109
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h110 | h110
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h111 | h111
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h112 | h112
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h113 | h113
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h115 | h115
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h116 | h116
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h119 | h119
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h120 | h120
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                                                    · linarith only [h100, h121, hlam]
                                                    · linarith only [h108, h112, h114, h116, h120, h121, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                                                    · linarith only [h100, h124, hlam]
                                                    · linarith only [h108, h112, h114, h116, h124, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                                · linarith only [h119, h9, hlam]
                                              · linarith only [h118, h7, hlam]
                                            · linarith only [h117, h5, hlam]
                                          · linarith only [h106, h116, hc05, hlam, hphi, p11_1, u0ehi3]
                                        · linarith only [h115, hlam, p11_0]
                                      · linarith only [h114, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h100, h111, h113, hc01, hc25, hlam, hphi, ht12, p11_1, u0ehi1, u1ehi4]
                                  · linarith only [h100, h111, h112, hc01, hc23, hlam, hphi, ht12, p11_1, u0ehi1, u1ehi4]
                                · linarith only [h100, h111, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                              · linarith only [h110, h7, hlam, p0_1]
                            · linarith only [h109, hc13, hlam, hphi, p0_1, u1ehi1]
                          · linarith only [h108, hlam, p0_0]
                · linarith only [h99, hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h140 | h140
                · rcases p11_3 (m.d 1 5) (by simp) with h141 | h141
                  · linarith only [h141, h9, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p11_3 (m.d 2 5) (by simp) with h143 | h143
                    · linarith only [h141, h143, hc25, hlam, hphi, ht12, p11_1, u1ehi4]
                    · rcases p11_3 (m.d 3 5) (by simp) with h145 | h145
                      · linarith only [h141, h145, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi4]
                      · rcases p11_3 (m.d 4 5) (by simp) with h147 | h147
                        · linarith only [h147, hlam, p11_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h149 | h149
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h150 | h150
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h151 | h151
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h153 | h153
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h154 | h154
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h155 | h155
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h156 | h156
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h157 | h157
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                                                      · linarith only [h141, h163, hlam]
                                                      · linarith only [h153, h155, h157, h163, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi3]
                                                    · linarith only [h145, h149, h153, h155, h157, h161, h162, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h167 | h167
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h168 | h168
                                                      · linarith only [h141, h168, hlam]
                                                      · linarith only [h149, h153, h155, h157, h161, h167, h168, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi4]
                                                    · linarith only [h145, h149, h153, h155, h157, h167, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                                · linarith only [h160, h9, hlam]
                                              · linarith only [h159, h7, hlam]
                                            · linarith only [h158, h5, hlam]
                                          · linarith only [h157, hlam, p11_0]
                                        · linarith only [h145, h156, hc05, hlam, hphi, p11_1, u0ehi2]
                                      · linarith only [h141, h149, h154, h155, hc01, hc34, hlam, hphi, ht12, ht23, p11_1, u0ehi2, u1ehi4]
                                    · linarith only [h154, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                                  · linarith only [h141, h152, h153, hc01, hc23, hlam, hphi, ht12, p11_1, u0ehi1, u1ehi4]
                                · linarith only [h141, h152, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                              · linarith only [h151, hc14, hlam, hphi, p0_1, u1ehi1]
                            · linarith only [h150, hc13, hlam, hphi, p0_1, u1ehi1]
                          · linarith only [h149, hlam, p0_0]
                · linarith only [h140, hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [h9, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc25, hlam, hphi, ht01, ht12, p11_1, u0ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc25, hlam, hphi, ht12, p11_1, u1ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h193 | h193
                · rcases p11_3 (m.d 1 5) (by simp) with h194 | h194
                  · linarith only [h194, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h194, hc25, hlam, hphi, ht12, p11_1, u1ehi4]
                · linarith only [h193, hc25, hlam, hphi, ht01, ht12, p11_1, u0ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h198 | h198
                · rcases p11_3 (m.d 1 5) (by simp) with h199 | h199
                  · linarith only [h199, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h199, hc25, hlam, hphi, ht12, p11_1, u1ehi4]
                · linarith only [h198, hc25, hlam, hphi, ht01, ht12, p11_1, u0ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h205 | h205
                · rcases p11_3 (m.d 1 5) (by simp) with h206 | h206
                  · linarith only [h206, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h206, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi4]
                · linarith only [h205, hc35, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h211 | h211
                · rcases p11_3 (m.d 1 5) (by simp) with h212 | h212
                  · linarith only [h212, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h212, hc35, hlam, hphi, ht12, ht23, p11_1, u1ehi4]
                · linarith only [h211, hc35, hlam, hphi, ht01, ht12, ht23, p11_1, u0ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p11_1, u0ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p11_1, u1ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h218 | h218
                · rcases p11_3 (m.d 1 5) (by simp) with h219 | h219
                  · linarith only [h219, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h219, hc45, hlam, hphi, ht12, ht23, ht34, p11_1, u1ehi4]
                · linarith only [h218, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p11_1, u0ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 5) (by simp) with h223 | h223
                · rcases p11_3 (m.d 1 5) (by simp) with h224 | h224
                  · linarith only [h224, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h224, hc45, hlam, hphi, ht12, ht23, ht34, p11_1, u1ehi4]
                · linarith only [h223, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p11_1, u0ehi4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h230 | h230
    · rcases p0_3 (m.d 1 2) (by simp) with h231 | h231
      · linarith only [h231, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h233 | h233
        · linarith only [h233, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h235 | h235
          · linarith only [h235, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h237 | h237
            · linarith only [h237, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases h5bigk with h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hlam, p239_0]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h241 | h241
                · rcases p239_3 (m.d 1 5) (by simp) with h242 | h242
                  · linarith only [h242, hlam, p239_0]
                  · rcases p239_3 (m.d 2 5) (by simp) with h244 | h244
                    · linarith only [h244, hc25, hlam, hphi, ht12, p239_1, u1ehi4]
                    · rcases p239_3 (m.d 3 5) (by simp) with h246 | h246
                      · linarith only [h246, hc35, hlam, hphi, ht12, ht23, p239_1, u1ehi4]
                      · rcases p239_3 (m.d 4 5) (by simp) with h248 | h248
                        · linarith only [h248, hc45, hlam, hphi, ht12, ht23, ht34, p239_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h250 | h250
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h251 | h251
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h252 | h252
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h253 | h253
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h254 | h254
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h255 | h255
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h256 | h256
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h257 | h257
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h258 | h258
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h259 | h259
                                            · linarith only [h231, h259, hlam]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h261 | h261
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h263 | h263
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h264 | h264
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h265 | h265
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h266 | h266
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h267 | h267
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h268 | h268
                                                            · linarith only [h259, h261, h268, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                                            · linarith only [h263, h265, h266, h268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                          · linarith only [h259, h267, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                                        · linarith only [h259, h261, h265, h266, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                                      · linarith only [h248, h265, hlam]
                                                    · linarith only [h246, h264, hlam]
                                                  · linarith only [h235, h263, hlam]
                                                · linarith only [h244, h262, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h277 | h277
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h283 | h283
                                                            · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                                                              · linarith only [h278, h284, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                                              · linarith only [h278, h280, h284, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                            · linarith only [h261, h278, h280, h283, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                                                          · linarith only [h261, h277, h279, h281, h282, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
                                                        · linarith only [h259, h277, h281, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                                      · linarith only [h248, h280, hlam]
                                                    · linarith only [h246, h279, hlam]
                                                  · linarith only [h235, h278, hlam]
                                                · linarith only [h244, h277, hlam]
                                          · linarith only [h258, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                                        · linarith only [h250, h255, h257, hc01, hc35, hlam, hphi, ht12, ht23, p239_1, u0ehi2, u1ehi4]
                                      · linarith only [h250, h255, h256, hc01, hc34, hlam, hphi, ht12, ht23, p239_1, u0ehi2, u1ehi4]
                                    · linarith only [h255, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                                  · linarith only [h253, h254, hc01, hc23, hlam, hphi, ht12, p239_1, u0ehi1, u1ehi4]
                                · linarith only [h253, hlam, p239_0]
                              · linarith only [h252, hc14, hlam, hphi, ht01, u0ehi0]
                            · linarith only [h251, hlam, p0_0]
                          · linarith only [h231, h250, hlam, p0_1]
                · linarith only [h241, hlam, p239_0]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h304 | h304
                · rcases p239_3 (m.d 1 5) (by simp) with h305 | h305
                  · linarith only [h237, h305, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p239_3 (m.d 2 5) (by simp) with h307 | h307
                    · linarith only [h307, hlam, p239_0]
                    · rcases p239_3 (m.d 3 5) (by simp) with h309 | h309
                      · linarith only [h305, h309, hc35, hlam, hphi, ht12, ht23, p239_1, u1ehi4]
                      · rcases p239_3 (m.d 4 5) (by simp) with h311 | h311
                        · linarith only [h305, h311, hc45, hlam, hphi, ht12, ht23, ht34, p239_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h313 | h313
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h314 | h314
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h315 | h315
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h316 | h316
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h317 | h317
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h318 | h318
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h319 | h319
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h320 | h320
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h321 | h321
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h322 | h322
                                            · linarith only [h231, h322, hlam]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h324 | h324
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h325 | h325
                                                · linarith only [h305, h325, hlam]
                                                · linarith only [h317, h319, h321, h324, h325, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p239_1]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h328 | h328
                                                · linarith only [h305, h328, hlam]
                                                · linarith only [h313, h317, h319, h321, h328, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p239_1, u1ehi1]
                                          · linarith only [h311, h321, hc05, hlam, hphi, p239_1, u0ehi3]
                                        · linarith only [h309, h313, h318, h319, h320, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p239_1]
                                      · linarith only [h319, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h318, hlam, p239_0]
                                  · linarith only [h305, h316, h317, hc01, hc23, hlam, hphi, ht12, p239_1, u0ehi1, u1ehi4]
                                · linarith only [h305, h316, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p239_1, u1ehi0]
                              · linarith only [h235, h315, hlam, p0_1]
                            · linarith only [h314, hlam, p0_0]
                          · linarith only [h313, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h304, hlam, p239_0]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h341 | h341
                · rcases p239_3 (m.d 1 5) (by simp) with h342 | h342
                  · linarith only [h237, h342, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p239_3 (m.d 2 5) (by simp) with h344 | h344
                    · linarith only [h342, h344, hc25, hlam, hphi, ht12, p239_1, u1ehi4]
                    · rcases p239_3 (m.d 3 5) (by simp) with h346 | h346
                      · linarith only [h346, hlam, p239_0]
                      · rcases p239_3 (m.d 4 5) (by simp) with h348 | h348
                        · linarith only [h342, h348, hc45, hlam, hphi, ht12, ht23, ht34, p239_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h350 | h350
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h351 | h351
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h352 | h352
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h353 | h353
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h354 | h354
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h355 | h355
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h356 | h356
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h357 | h357
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h358 | h358
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h359 | h359
                                            · linarith only [h231, h359, hlam]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h361 | h361
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h362 | h362
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h363 | h363
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h364 | h364
                                                    · linarith only [h342, h364, hlam]
                                                    · linarith only [h237, h364, hlam]
                                                  · linarith only [h235, h363, hlam]
                                                · linarith only [h344, h350, h354, h356, h358, h361, h362, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p239_1]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h369 | h369
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h370 | h370
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h371 | h371
                                                    · linarith only [h342, h371, hlam]
                                                    · linarith only [h237, h371, hlam]
                                                  · linarith only [h235, h370, hlam]
                                                · linarith only [h344, h350, h354, h356, h358, h369, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p239_1, u1ehi1]
                                          · linarith only [h348, h350, h354, h357, h358, hc01, hlam, hphi, p239_1, u0ehi3]
                                        · linarith only [h357, hlam, p239_0]
                                      · linarith only [h356, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h344, h353, h354, h355, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p239_1]
                                  · linarith only [h342, h353, h354, hc01, hc23, hlam, hphi, ht12, p239_1, u0ehi1, u1ehi4]
                                · linarith only [h342, h353, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p239_1, u1ehi0]
                              · linarith only [h352, hc14, hlam, hphi, p0_1, u1ehi2]
                            · linarith only [h351, hlam, p0_0]
                          · linarith only [h350, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h341, hlam, p239_0]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h386 | h386
                · rcases p239_3 (m.d 1 5) (by simp) with h387 | h387
                  · linarith only [h237, h387, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p239_3 (m.d 2 5) (by simp) with h389 | h389
                    · linarith only [h387, h389, hc25, hlam, hphi, ht12, p239_1, u1ehi4]
                    · rcases p239_3 (m.d 3 5) (by simp) with h391 | h391
                      · linarith only [h387, h391, hc35, hlam, hphi, ht12, ht23, p239_1, u1ehi4]
                      · rcases p239_3 (m.d 4 5) (by simp) with h393 | h393
                        · linarith only [h393, hlam, p239_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h395 | h395
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h396 | h396
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h397 | h397
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h398 | h398
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h399 | h399
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h400 | h400
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h401 | h401
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h402 | h402
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h403 | h403
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
                                            · linarith only [h231, h404, hlam]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h406 | h406
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h407 | h407
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                                                      · linarith only [h387, h410, hlam]
                                                      · linarith only [h399, h401, h403, h410, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p239_1, u1ehi3]
                                                    · linarith only [h237, h409, hlam]
                                                  · linarith only [h235, h408, hlam]
                                                · linarith only [h389, h395, h399, h401, h403, h406, h407, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p239_1]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h416 | h416
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h417 | h417
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h419 | h419
                                                      · linarith only [h387, h419, hlam]
                                                      · linarith only [h395, h399, h401, h403, h406, h416, h419, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p239_1, u1ehi4]
                                                    · linarith only [h237, h418, hlam]
                                                  · linarith only [h235, h417, hlam]
                                                · linarith only [h389, h395, h399, h401, h403, h416, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p239_1, u1ehi1]
                                          · linarith only [h403, hlam, p239_0]
                                        · linarith only [h402, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                      · linarith only [h387, h395, h400, h401, hc01, hc34, hlam, hphi, ht12, ht23, p239_1, u0ehi2, u1ehi4]
                                    · linarith only [h389, h399, h400, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p239_1]
                                  · linarith only [h399, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                                · linarith only [h387, h398, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p239_1, u1ehi0]
                              · linarith only [h397, hc14, hlam, hphi, p0_1, u1ehi2]
                            · linarith only [h396, hlam, p0_0]
                          · linarith only [h395, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h386, hlam, p239_0]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [h237, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hlam, p239_0]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [h237, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [h237, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [h237, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hc25, hlam, hphi, ht01, ht12, p239_1, u0ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hc25, hlam, hphi, ht12, p239_1, u1ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hlam, p239_0]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h443 | h443
                · rcases p239_3 (m.d 1 5) (by simp) with h444 | h444
                  · linarith only [h237, h444, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
                  · linarith only [h444, hc25, hlam, hphi, ht12, p239_1, u1ehi4]
                · linarith only [h443, hc25, hlam, hphi, ht01, ht12, p239_1, u0ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h448 | h448
                · rcases p239_3 (m.d 1 5) (by simp) with h449 | h449
                  · linarith only [h237, h449, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
                  · linarith only [h449, hc25, hlam, hphi, ht12, p239_1, u1ehi4]
                · linarith only [h448, hc25, hlam, hphi, ht01, ht12, p239_1, u0ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p239_1, u0ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hc35, hlam, hphi, ht12, ht23, p239_1, u1ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h455 | h455
                · rcases p239_3 (m.d 1 5) (by simp) with h456 | h456
                  · linarith only [h237, h456, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
                  · linarith only [h456, hc35, hlam, hphi, ht12, ht23, p239_1, u1ehi4]
                · linarith only [h455, hc35, hlam, hphi, ht01, ht12, ht23, p239_1, u0ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hlam, p239_0]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h461 | h461
                · rcases p239_3 (m.d 1 5) (by simp) with h462 | h462
                  · linarith only [h237, h462, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
                  · linarith only [h462, hc35, hlam, hphi, ht12, ht23, p239_1, u1ehi4]
                · linarith only [h461, hc35, hlam, hphi, ht01, ht12, ht23, p239_1, u0ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p239_1, u0ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p239_1, u1ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h468 | h468
                · rcases p239_3 (m.d 1 5) (by simp) with h469 | h469
                  · linarith only [h237, h469, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
                  · linarith only [h469, hc45, hlam, hphi, ht12, ht23, ht34, p239_1, u1ehi4]
                · linarith only [h468, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p239_1, u0ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                rcases p239_3 (m.d 0 5) (by simp) with h473 | h473
                · rcases p239_3 (m.d 1 5) (by simp) with h474 | h474
                  · linarith only [h237, h474, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p239_1]
                  · linarith only [h474, hc45, hlam, hphi, ht12, ht23, ht34, p239_1, u1ehi4]
                · linarith only [h473, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p239_1, u0ehi4]
              · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                linarith only [hlam, p239_0]
    · linarith only [h230, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h480 | h480
    · rcases p0_3 (m.d 1 2) (by simp) with h481 | h481
      · linarith only [h481, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h483 | h483
        · linarith only [h483, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h485 | h485
          · linarith only [h485, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h487 | h487
            · linarith only [h487, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases h5bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hlam, p489_0]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h491 | h491
                · rcases p489_3 (m.d 1 5) (by simp) with h492 | h492
                  · linarith only [h492, hlam, p489_0]
                  · rcases p489_3 (m.d 2 5) (by simp) with h494 | h494
                    · linarith only [h494, hc25, hlam, hphi, ht12, p489_1, u1ehi4]
                    · rcases p489_3 (m.d 3 5) (by simp) with h496 | h496
                      · linarith only [h496, hc35, hlam, hphi, ht12, ht23, p489_1, u1ehi4]
                      · rcases p489_3 (m.d 4 5) (by simp) with h498 | h498
                        · linarith only [h498, hc45, hlam, hphi, ht12, ht23, ht34, p489_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h500 | h500
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h501 | h501
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h502 | h502
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h503 | h503
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h504 | h504
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h505 | h505
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h506 | h506
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h507 | h507
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h508 | h508
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h509 | h509
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h510 | h510
                                              · linarith only [h481, h510, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h512 | h512
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h513 | h513
                                                  · linarith only [h483, h513, hlam]
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h515 | h515
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h516 | h516
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h517 | h517
                                                        · linarith only [h509, h510, h517, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h519 | h519
                                                          · linarith only [h500, h504, h506, h509, h510, h517, h519, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                                          · linarith only [h500, h504, h506, h509, h510, h515, h517, h519, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                                      · linarith only [h498, h516, hlam]
                                                    · linarith only [h496, h515, hlam]
                                                · linarith only [h494, h512, hlam]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h525 | h525
                                              · linarith only [h481, h525, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h527 | h527
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h528 | h528
                                                  · linarith only [h483, h528, hlam]
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h530 | h530
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h531 | h531
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h532 | h532
                                                        · linarith only [h509, h527, h528, h532, hc23, hlam, hphi, ht12, u1ehi4]
                                                        · linarith only [h509, h527, h532, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                                      · linarith only [h498, h531, hlam]
                                                    · linarith only [h496, h530, hlam]
                                                · linarith only [h494, h527, hlam]
                                          · linarith only [h508, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                                        · linarith only [h500, h505, h507, hc01, hc35, hlam, hphi, ht12, ht23, p489_1, u0ehi2, u1ehi4]
                                      · linarith only [h500, h505, h506, hc01, hc34, hlam, hphi, ht12, ht23, p489_1, u0ehi2, u1ehi4]
                                    · linarith only [h505, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                                  · linarith only [h503, h504, hc01, hc23, hlam, hphi, ht12, p489_1, u0ehi1, u1ehi4]
                                · linarith only [h503, hlam, p489_0]
                              · linarith only [h502, hlam, p0_0]
                            · linarith only [h501, hc13, hlam, hphi, ht01, u0ehi0]
                          · linarith only [h500, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h491, hlam, p489_0]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h548 | h548
                · rcases p489_3 (m.d 1 5) (by simp) with h549 | h549
                  · linarith only [h487, h549, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p489_3 (m.d 2 5) (by simp) with h551 | h551
                    · linarith only [h551, hlam, p489_0]
                    · rcases p489_3 (m.d 3 5) (by simp) with h553 | h553
                      · linarith only [h549, h553, hc35, hlam, hphi, ht12, ht23, p489_1, u1ehi4]
                      · rcases p489_3 (m.d 4 5) (by simp) with h555 | h555
                        · linarith only [h549, h555, hc45, hlam, hphi, ht12, ht23, ht34, p489_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h557 | h557
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h558 | h558
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h559 | h559
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h560 | h560
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h561 | h561
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h562 | h562
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h563 | h563
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h564 | h564
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h565 | h565
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h566 | h566
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
                                              · linarith only [h481, h567, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                                                · linarith only [h549, h569, hlam]
                                                · linarith only [h561, h563, h565, h566, h569, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h572 | h572
                                              · linarith only [h481, h572, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h574 | h574
                                                · linarith only [h549, h574, hlam]
                                                · linarith only [h557, h561, h563, h565, h574, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi1]
                                          · linarith only [h555, h565, hc05, hlam, hphi, p489_1, u0ehi3]
                                        · linarith only [h553, h557, h562, h563, h564, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p489_1]
                                      · linarith only [h563, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h562, hlam, p489_0]
                                  · linarith only [h549, h560, h561, hc01, hc23, hlam, hphi, ht12, p489_1, u0ehi1, u1ehi4]
                                · linarith only [h549, h560, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi0]
                              · linarith only [h559, hlam, p0_0]
                            · linarith only [h483, h558, hlam, p0_1]
                          · linarith only [h483, h557, hc12, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h548, hlam, p489_0]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h587 | h587
                · rcases p489_3 (m.d 1 5) (by simp) with h588 | h588
                  · linarith only [h487, h588, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p489_3 (m.d 2 5) (by simp) with h590 | h590
                    · linarith only [h588, h590, hc25, hlam, hphi, ht12, p489_1, u1ehi4]
                    · rcases p489_3 (m.d 3 5) (by simp) with h592 | h592
                      · linarith only [h592, hlam, p489_0]
                      · rcases p489_3 (m.d 4 5) (by simp) with h594 | h594
                        · linarith only [h588, h594, hc45, hlam, hphi, ht12, ht23, ht34, p489_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h596 | h596
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h597 | h597
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h598 | h598
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h599 | h599
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h600 | h600
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h601 | h601
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h602 | h602
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h603 | h603
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h604 | h604
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h605 | h605
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h606 | h606
                                              · linarith only [h481, h606, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h609 | h609
                                                  · linarith only [h483, h609, hlam]
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
                                                    · linarith only [h588, h611, hlam]
                                                    · linarith only [h600, h602, h604, h611, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi2]
                                                · linarith only [h590, h596, h600, h602, h604, h605, h608, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h615 | h615
                                              · linarith only [h481, h615, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h617 | h617
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h618 | h618
                                                  · linarith only [h483, h618, hlam]
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h620 | h620
                                                    · linarith only [h588, h620, hlam]
                                                    · linarith only [h596, h600, h602, h604, h605, h617, h620, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi4]
                                                · linarith only [h590, h596, h600, h602, h604, h617, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi1]
                                          · linarith only [h594, h604, hc05, hlam, hphi, p489_1, u0ehi3]
                                        · linarith only [h603, hlam, p489_0]
                                      · linarith only [h602, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h588, h599, h601, hc01, hc25, hlam, hphi, ht12, p489_1, u0ehi1, u1ehi4]
                                  · linarith only [h588, h599, h600, hc01, hc23, hlam, hphi, ht12, p489_1, u0ehi1, u1ehi4]
                                · linarith only [h588, h599, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi0]
                              · linarith only [h598, hlam, p0_0]
                            · linarith only [h597, hc13, hlam, hphi, p0_1, u1ehi3]
                          · linarith only [h596, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h587, hlam, p489_0]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h634 | h634
                · rcases p489_3 (m.d 1 5) (by simp) with h635 | h635
                  · linarith only [h487, h635, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p489_3 (m.d 2 5) (by simp) with h637 | h637
                    · linarith only [h635, h637, hc25, hlam, hphi, ht12, p489_1, u1ehi4]
                    · rcases p489_3 (m.d 3 5) (by simp) with h639 | h639
                      · linarith only [h635, h639, hc35, hlam, hphi, ht12, ht23, p489_1, u1ehi4]
                      · rcases p489_3 (m.d 4 5) (by simp) with h641 | h641
                        · linarith only [h641, hlam, p489_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h643 | h643
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h644 | h644
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h645 | h645
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h646 | h646
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h647 | h647
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h648 | h648
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h649 | h649
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h650 | h650
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h651 | h651
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h653 | h653
                                              · linarith only [h481, h653, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h655 | h655
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h656 | h656
                                                  · linarith only [h483, h656, hlam]
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h658 | h658
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h659 | h659
                                                      · linarith only [h635, h659, hlam]
                                                      · linarith only [h487, h659, hlam]
                                                    · linarith only [h639, h647, h649, h651, h658, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi2]
                                                · linarith only [h637, h643, h647, h649, h651, h652, h655, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h664 | h664
                                              · linarith only [h481, h664, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h666 | h666
                                                · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                                                  · linarith only [h483, h667, hlam]
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h669 | h669
                                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h670 | h670
                                                      · linarith only [h635, h670, hlam]
                                                      · linarith only [h487, h670, hlam]
                                                    · linarith only [h639, h643, h647, h649, h651, h652, h666, h669, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi4]
                                                · linarith only [h637, h643, h647, h649, h651, h666, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi1]
                                          · linarith only [h651, hlam, p489_0]
                                        · linarith only [h639, h649, h650, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p489_1]
                                      · linarith only [h649, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h637, h646, h648, hc01, hlam, hphi, p489_1, u0ehi1]
                                  · linarith only [h635, h646, h647, hc01, hc23, hlam, hphi, ht12, p489_1, u0ehi1, u1ehi4]
                                · linarith only [h635, h646, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p489_1, u1ehi0]
                              · linarith only [h645, hlam, p0_0]
                            · linarith only [h644, hc13, hlam, hphi, p0_1, u1ehi3]
                          · linarith only [h643, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h634, hlam, p489_0]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [h487, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hlam, p489_0]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [h487, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [h487, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [h487, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hc25, hlam, hphi, ht01, ht12, p489_1, u0ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hc25, hlam, hphi, ht12, p489_1, u1ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hlam, p489_0]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h693 | h693
                · rcases p489_3 (m.d 1 5) (by simp) with h694 | h694
                  · linarith only [h487, h694, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
                  · linarith only [h694, hc25, hlam, hphi, ht12, p489_1, u1ehi4]
                · linarith only [h693, hc25, hlam, hphi, ht01, ht12, p489_1, u0ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h698 | h698
                · rcases p489_3 (m.d 1 5) (by simp) with h699 | h699
                  · linarith only [h487, h699, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
                  · linarith only [h699, hc25, hlam, hphi, ht12, p489_1, u1ehi4]
                · linarith only [h698, hc25, hlam, hphi, ht01, ht12, p489_1, u0ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p489_1, u0ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hc35, hlam, hphi, ht12, ht23, p489_1, u1ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h705 | h705
                · rcases p489_3 (m.d 1 5) (by simp) with h706 | h706
                  · linarith only [h487, h706, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
                  · linarith only [h706, hc35, hlam, hphi, ht12, ht23, p489_1, u1ehi4]
                · linarith only [h705, hc35, hlam, hphi, ht01, ht12, ht23, p489_1, u0ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hlam, p489_0]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h711 | h711
                · rcases p489_3 (m.d 1 5) (by simp) with h712 | h712
                  · linarith only [h487, h712, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
                  · linarith only [h712, hc35, hlam, hphi, ht12, ht23, p489_1, u1ehi4]
                · linarith only [h711, hc35, hlam, hphi, ht01, ht12, ht23, p489_1, u0ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p489_1, u0ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p489_1, u1ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h718 | h718
                · rcases p489_3 (m.d 1 5) (by simp) with h719 | h719
                  · linarith only [h487, h719, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
                  · linarith only [h719, hc45, hlam, hphi, ht12, ht23, ht34, p489_1, u1ehi4]
                · linarith only [h718, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p489_1, u0ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                rcases p489_3 (m.d 0 5) (by simp) with h723 | h723
                · rcases p489_3 (m.d 1 5) (by simp) with h724 | h724
                  · linarith only [h487, h724, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p489_1]
                  · linarith only [h724, hc45, hlam, hphi, ht12, ht23, ht34, p489_1, u1ehi4]
                · linarith only [h723, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p489_1, u0ehi4]
              · obtain ⟨p489_0, p489_1, p489_2, p489_3⟩ := h489c
                linarith only [hlam, p489_0]
    · linarith only [h480, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h730 | h730
    · rcases p0_3 (m.d 1 2) (by simp) with h731 | h731
      · linarith only [h731, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h733 | h733
        · linarith only [h733, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h735 | h735
          · linarith only [h735, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h737 | h737
            · linarith only [h737, hlam, p0_0]
            · rcases h5bigk with h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hlam, p739_0]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h741 | h741
                · rcases p739_3 (m.d 1 5) (by simp) with h742 | h742
                  · linarith only [h742, hlam, p739_0]
                  · rcases p739_3 (m.d 2 5) (by simp) with h744 | h744
                    · linarith only [h744, hc25, hlam, hphi, ht12, p739_1, u1ehi4]
                    · rcases p739_3 (m.d 3 5) (by simp) with h746 | h746
                      · linarith only [h746, hc35, hlam, hphi, ht12, ht23, p739_1, u1ehi4]
                      · rcases p739_3 (m.d 4 5) (by simp) with h748 | h748
                        · linarith only [h748, hc45, hlam, hphi, ht12, ht23, ht34, p739_1, u1ehi4]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h750 | h750
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h751 | h751
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h752 | h752
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h753 | h753
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h754 | h754
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h755 | h755
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h756 | h756
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h757 | h757
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h758 | h758
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h759 | h759
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h760 | h760
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h761 | h761
                                                · linarith only [h731, h761, hlam]
                                                · linarith only [h744, h761, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h764 | h764
                                                · linarith only [h731, h764, hlam]
                                                · linarith only [h744, h764, hlam]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h767 | h767
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h768 | h768
                                                · linarith only [h731, h768, hlam]
                                                · linarith only [h744, h768, hlam]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h771 | h771
                                                · linarith only [h731, h771, hlam]
                                                · linarith only [h744, h771, hlam]
                                          · linarith only [h748, h758, hc05, hlam, hphi, p739_1, u0ehi3]
                                        · linarith only [h746, h750, h755, h756, h757, hc01, hlam, hphi, p739_1, u0ehi3]
                                      · linarith only [h750, h755, h756, hc01, hc34, hlam, hphi, ht12, ht23, p739_1, u0ehi2, u1ehi4]
                                    · linarith only [h744, h755, hc05, hlam, hphi, p739_1, u0ehi1]
                                  · linarith only [h753, h754, hc01, hc23, hlam, hphi, ht12, p739_1, u0ehi1, u1ehi4]
                                · linarith only [h753, hlam, p0_0]
                              · linarith only [h752, hc14, hlam, hphi, ht01, u0ehi0]
                            · linarith only [h751, hc13, hlam, hphi, p0_1, u1ehi4]
                          · linarith only [h750, hc12, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h741, hlam, p739_0]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h784 | h784
                · rcases p739_3 (m.d 1 5) (by simp) with h785 | h785
                  · linarith only [h785, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p739_3 (m.d 2 5) (by simp) with h787 | h787
                    · linarith only [h787, hlam, p739_0]
                    · rcases p739_3 (m.d 3 5) (by simp) with h789 | h789
                      · linarith only [h731, h785, h789, hc35, hlam, hphi, ht12, ht23, p739_1, u1ehi1]
                      · rcases p739_3 (m.d 4 5) (by simp) with h791 | h791
                        · linarith only [h731, h785, h791, hc45, hlam, hphi, ht12, ht23, ht34, p739_1, u1ehi1]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h793 | h793
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h794 | h794
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h795 | h795
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h796 | h796
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h797 | h797
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h798 | h798
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h799 | h799
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h800 | h800
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h801 | h801
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h803 | h803
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h804 | h804
                                                · linarith only [h731, h804, hlam]
                                                · linarith only [h793, h797, h799, h801, h802, h804, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi2]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h807 | h807
                                                · linarith only [h731, h807, hlam]
                                                · linarith only [h793, h797, h799, h801, h802, h807, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi2]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h810 | h810
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h811 | h811
                                                · linarith only [h731, h811, hlam]
                                                · linarith only [h793, h797, h799, h801, h810, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi3]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h814 | h814
                                                · linarith only [h731, h814, hlam]
                                                · linarith only [h793, h797, h799, h801, h814, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi1]
                                          · linarith only [h791, h801, hc05, hlam, hphi, p739_1, u0ehi3]
                                        · linarith only [h789, h793, h798, h799, h800, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p739_1]
                                      · linarith only [h799, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h798, hlam, p739_0]
                                  · linarith only [h785, h796, h797, hc01, hc23, hlam, hphi, ht12, p739_1, u0ehi1, u1ehi4]
                                · linarith only [h796, hlam, p0_0]
                              · linarith only [h795, hc14, hlam, hphi, ht01, u0ehi0]
                            · linarith only [h794, hc13, hlam, hphi, p0_1, u1ehi4]
                          · linarith only [h793, hc12, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h784, hlam, p739_0]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h827 | h827
                · rcases p739_3 (m.d 1 5) (by simp) with h828 | h828
                  · linarith only [h828, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p739_3 (m.d 2 5) (by simp) with h830 | h830
                    · linarith only [h731, h828, h830, hc25, hlam, hphi, ht12, p739_1, u1ehi1]
                    · rcases p739_3 (m.d 3 5) (by simp) with h832 | h832
                      · linarith only [h832, hlam, p739_0]
                      · rcases p739_3 (m.d 4 5) (by simp) with h834 | h834
                        · linarith only [h731, h828, h834, hc45, hlam, hphi, ht12, ht23, ht34, p739_1, u1ehi1]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h836 | h836
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h837 | h837
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h838 | h838
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h839 | h839
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h840 | h840
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h841 | h841
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h842 | h842
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h843 | h843
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h844 | h844
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h845 | h845
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h846 | h846
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h847 | h847
                                                · linarith only [h731, h847, hlam]
                                                · linarith only [h830, h836, h840, h842, h844, h845, h847, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi2]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h850 | h850
                                                · linarith only [h731, h850, hlam]
                                                · linarith only [h830, h836, h840, h842, h844, h845, h850, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi2]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h853 | h853
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h854 | h854
                                                · linarith only [h731, h854, hlam]
                                                · linarith only [h830, h836, h840, h842, h844, h853, h854, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p739_1]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h857 | h857
                                                · linarith only [h731, h857, hlam]
                                                · linarith only [h830, h836, h840, h842, h844, h857, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi1]
                                          · linarith only [h834, h844, hc05, hlam, hphi, p739_1, u0ehi3]
                                        · linarith only [h843, hlam, p739_0]
                                      · linarith only [h733, h828, h836, h841, h842, hc01, hc34, hlam, hphi, ht12, ht23, p739_1, u0ehi2, u1ehi2]
                                    · linarith only [h830, h841, hc05, hlam, hphi, p739_1, u0ehi1]
                                  · linarith only [h733, h828, h839, h840, hc01, hc23, hlam, hphi, ht12, p739_1, u0ehi1, u1ehi2]
                                · linarith only [h839, hlam, p0_0]
                              · linarith only [h735, h828, h838, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi0]
                            · linarith only [h837, hc13, hlam, hphi, ht01, u0ehi0]
                          · linarith only [h735, h836, hc12, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h827, hlam, p739_0]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h870 | h870
                · rcases p739_3 (m.d 1 5) (by simp) with h871 | h871
                  · linarith only [h871, hc01, hlam, hphi, p0_1, u0ehi4]
                  · rcases p739_3 (m.d 2 5) (by simp) with h873 | h873
                    · linarith only [h731, h871, h873, hc25, hlam, hphi, ht12, p739_1, u1ehi1]
                    · rcases p739_3 (m.d 3 5) (by simp) with h875 | h875
                      · linarith only [h731, h871, h875, hc35, hlam, hphi, ht12, ht23, p739_1, u1ehi1]
                      · rcases p739_3 (m.d 4 5) (by simp) with h877 | h877
                        · linarith only [h877, hlam, p739_0]
                        · rcases m.htr 0 1 2 (by decide) (by decide) with h879 | h879
                          · rcases m.htr 0 1 3 (by decide) (by decide) with h880 | h880
                            · rcases m.htr 0 1 4 (by decide) (by decide) with h881 | h881
                              · rcases m.htr 0 1 5 (by decide) (by decide) with h882 | h882
                                · rcases m.htr 0 2 3 (by decide) (by decide) with h883 | h883
                                  · rcases m.htr 0 2 5 (by decide) (by decide) with h884 | h884
                                    · rcases m.htr 0 3 4 (by decide) (by decide) with h885 | h885
                                      · rcases m.htr 0 3 5 (by decide) (by decide) with h886 | h886
                                        · rcases m.htr 0 4 5 (by decide) (by decide) with h887 | h887
                                          · rcases m.htr 1 2 3 (by decide) (by decide) with h888 | h888
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h889 | h889
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h890 | h890
                                                · linarith only [h731, h890, hlam]
                                                · linarith only [h873, h879, h883, h885, h887, h888, h890, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi2]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h893 | h893
                                                · linarith only [h731, h893, hlam]
                                                · linarith only [h873, h879, h883, h885, h887, h888, h893, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi2]
                                            · rcases m.htr 1 2 4 (by decide) (by decide) with h896 | h896
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h897 | h897
                                                · linarith only [h731, h897, hlam]
                                                · linarith only [h873, h879, h883, h885, h887, h896, h897, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p739_1]
                                              · rcases m.htr 1 2 5 (by decide) (by decide) with h900 | h900
                                                · linarith only [h731, h900, hlam]
                                                · linarith only [h873, h879, h883, h885, h887, h900, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi1]
                                          · linarith only [h887, hlam, p739_0]
                                        · linarith only [h875, h885, h886, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p739_1]
                                      · linarith only [h885, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h873, h882, h884, hc01, hlam, hphi, p739_1, u0ehi1]
                                  · linarith only [h871, h882, h883, hc01, hc23, hlam, hphi, ht12, p739_1, u0ehi1, u1ehi4]
                                · linarith only [h882, hlam, p0_0]
                              · linarith only [h735, h871, h881, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p739_1, u1ehi0]
                            · linarith only [h733, h880, hlam, p0_1]
                          · linarith only [h879, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h870, hlam, p739_0]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hlam, p739_0]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hc25, hlam, hphi, ht01, ht12, p739_1, u0ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [h731, hc25, hlam, hphi, ht12, p739_1, u1ehi1]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hlam, p739_0]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h921 | h921
                · rcases p739_3 (m.d 1 5) (by simp) with h922 | h922
                  · linarith only [h922, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
                  · linarith only [h735, h922, hc25, hlam, hphi, ht12, p739_1, u1ehi3]
                · linarith only [h921, hc25, hlam, hphi, ht01, ht12, p739_1, u0ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h926 | h926
                · rcases p739_3 (m.d 1 5) (by simp) with h927 | h927
                  · linarith only [h927, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
                  · linarith only [h927, hc25, hlam, hphi, ht12, p739_1, u1ehi4]
                · linarith only [h926, hc25, hlam, hphi, ht01, ht12, p739_1, u0ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p739_1, u0ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hc35, hlam, hphi, ht12, ht23, p739_1, u1ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h933 | h933
                · rcases p739_3 (m.d 1 5) (by simp) with h934 | h934
                  · linarith only [h934, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
                  · linarith only [h934, hc35, hlam, hphi, ht12, ht23, p739_1, u1ehi4]
                · linarith only [h933, hc35, hlam, hphi, ht01, ht12, ht23, p739_1, u0ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hlam, p739_0]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h939 | h939
                · rcases p739_3 (m.d 1 5) (by simp) with h940 | h940
                  · linarith only [h940, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
                  · linarith only [h940, hc35, hlam, hphi, ht12, ht23, p739_1, u1ehi4]
                · linarith only [h939, hc35, hlam, hphi, ht01, ht12, ht23, p739_1, u0ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p739_1, u0ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p739_1, u1ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h946 | h946
                · rcases p739_3 (m.d 1 5) (by simp) with h947 | h947
                  · linarith only [h947, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
                  · linarith only [h947, hc45, hlam, hphi, ht12, ht23, ht34, p739_1, u1ehi4]
                · linarith only [h946, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p739_1, u0ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                rcases p739_3 (m.d 0 5) (by simp) with h951 | h951
                · rcases p739_3 (m.d 1 5) (by simp) with h952 | h952
                  · linarith only [h952, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1, p739_1]
                  · linarith only [h952, hc45, hlam, hphi, ht12, ht23, ht34, p739_1, u1ehi4]
                · linarith only [h951, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p739_1, u0ehi4]
              · obtain ⟨p739_0, p739_1, p739_2, p739_3⟩ := h739c
                linarith only [hlam, p739_0]
    · linarith only [h730, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_H_R_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                                  · linarith only [h21, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                                  · linarith only [h21, h9, hlam]
                                · linarith only [h20, h7, hlam]
                              · linarith only [h19, h5, hlam]
                            · linarith only [h18, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                          · linarith only [h17, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h16, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h15, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h14, h9, hlam, p0_1]
                  · linarith only [h13, h9, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
                · linarith only [h12, hc13, hlam, hphi, p0_1, u1ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h35 | h35
    · rcases p0_3 (m.d 1 2) (by simp) with h36 | h36
      · linarith only [h36, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h38 | h38
        · linarith only [h38, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h40 | h40
          · linarith only [h40, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h42 | h42
            · linarith only [h42, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h44 | h44
              · rcases m.htr 0 1 3 (by decide) (by decide) with h45 | h45
                · rcases m.htr 0 1 4 (by decide) (by decide) with h46 | h46
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h51 | h51
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
                              · linarith only [h36, h52, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                                  · linarith only [h52, h55, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                                      · linarith only [h58, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                      · linarith only [h42, h58, hlam]
                                    · linarith only [h40, h57, hlam]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h62 | h62
                                  · linarith only [h48, h52, h62, hc02, hlam, hphi, ht0b, ht5b, u5ehi2]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                                      · linarith only [h65, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                      · linarith only [h42, h65, hlam]
                                    · linarith only [h40, h64, hlam]
                            · linarith only [h51, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                          · linarith only [h50, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h49, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h48, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h47, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h46, hc14, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h45, hlam, p0_0]
              · linarith only [h44, hc12, hlam, hphi, p0_1, u1ehi2]
    · linarith only [h35, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h78 | h78
    · rcases p0_3 (m.d 1 2) (by simp) with h79 | h79
      · linarith only [h79, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h81 | h81
        · linarith only [h81, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h83 | h83
          · linarith only [h83, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h85 | h85
            · linarith only [h85, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
              · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h92 | h92
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h93 | h93
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h94 | h94
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                                · linarith only [h79, h96, hlam]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
                                  · linarith only [h96, h98, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                                    · linarith only [h100, h81, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                                      · linarith only [h102, h95, h96, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                                        · linarith only [h104, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                        · linarith only [h104, h85, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                                · linarith only [h107, h79, hlam]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                                  · linarith only [h107, h109, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                                    · linarith only [h111, h81, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                                      · linarith only [h111, h113, h87, h91, h93, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                                        · linarith only [h115, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                        · linarith only [h115, h85, hlam]
                            · linarith only [h94, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                          · linarith only [h93, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h92, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h91, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h85, h90, hlam, p0_1]
                  · linarith only [h89, hlam, p0_0]
                · linarith only [h81, h88, hlam, p0_1]
              · linarith only [h85, h87, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
    · linarith only [h78, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h127 | h127
    · rcases p0_3 (m.d 1 2) (by simp) with h128 | h128
      · linarith only [h128, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h130 | h130
        · linarith only [h130, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h132 | h132
          · linarith only [h132, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h134 | h134
            · linarith only [h134, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 1 3 (by decide) (by decide) with h137 | h137
                · rcases m.htr 0 1 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h140 | h140
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h141 | h141
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h142 | h142
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h143 | h143
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h146 | h146
                                  · linarith only [h128, h146, hlam]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                                      · linarith only [h130, h149, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h151 | h151
                                        · linarith only [h132, h151, hlam]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                                          · linarith only [h144, h146, h153, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                          · linarith only [h144, h146, h148, h153, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
                                      · linarith only [h130, h156, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                                        · linarith only [h132, h158, hlam]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                                          · linarith only [h148, h160, hc23, hlam, hphi, ht12, u1ehi2]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                                            · linarith only [h145, h146, h160, h162, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                            · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                                              · linarith only [h145, h146, h164, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
                                                · linarith only [h145, h146, h160, h164, h166, hc23, hc34, hlam, hphi]
                                                · linarith only [h136, h140, h142, h143, h148, h166, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                                  · linarith only [h128, h169, hlam]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                                    · linarith only [h144, h145, h171, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                                      · linarith only [h130, h173, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                                        · linarith only [h132, h175, hlam]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                                          · linarith only [h171, h177, hc23, hlam, hphi, ht12, u1ehi2]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                                            · linarith only [h144, h145, h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                            · rcases m.htr 2 4 5 (by decide) (by decide) with h181 | h181
                                              · linarith only [h136, h140, h142, h144, h145, h175, h177, h181, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                              · linarith only [h136, h140, h142, h143, h144, h145, h181, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                                  · linarith only [h128, h185, hlam]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h188 | h188
                                      · linarith only [h130, h188, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h190 | h190
                                        · linarith only [h132, h190, hlam]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h192 | h192
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h193 | h193
                                            · linarith only [h144, h188, h193, hc23, hlam, hphi, ht12, u1ehi1]
                                            · linarith only [h144, h184, h193, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                          · linarith only [h144, h184, h192, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                    · linarith only [h144, h184, h187, hlam]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h198 | h198
                                  · linarith only [h128, h198, hlam]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h200 | h200
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                                      · linarith only [h130, h201, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                                        · linarith only [h132, h203, hlam]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h206 | h206
                                            · linarith only [h184, h200, h201, h206, hc23, hlam, hphi, ht12, u1ehi1]
                                            · linarith only [h144, h206, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                          · linarith only [h144, h200, h205, hc13, hlam, hphi, u1ehi1]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                                      · linarith only [h130, h210, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
                                        · linarith only [h132, h212, hlam]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                                          · linarith only [h144, h200, h214, hc23, hlam, hphi, ht12, u1ehi1]
                                          · linarith only [h144, h214, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h143, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                          · linarith only [h142, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h141, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h140, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h139, hlam, p0_0]
                  · linarith only [h132, h138, hlam, p0_1]
                · linarith only [h130, h137, hlam, p0_1]
              · linarith only [h136, hc12, hlam, hphi, p0_1, u1ehi4]
    · linarith only [h127, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_M_IR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h11, h14, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h11, h13, h14, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h11, h13, h17, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
                              · rcases h5bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p19_1, u1ehi4]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h22 | h22
                                  · rcases p19_3 (m.d 1 5) (by simp) with h23 | h23
                                    · linarith only [h23, h3, hlam]
                                    · linarith only [h23, h7, hlam]
                                  · linarith only [h22, h4, hlam]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h27 | h27
                                  · rcases p19_3 (m.d 1 5) (by simp) with h28 | h28
                                    · linarith only [h28, h3, hlam]
                                    · linarith only [h28, h9, hlam]
                                  · linarith only [h27, h5, hlam]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h32 | h32
                                  · rcases p19_3 (m.d 1 5) (by simp) with h33 | h33
                                    · linarith only [h3, h33, hlam]
                                    · linarith only [h10, h33, hlam]
                                  · linarith only [h32, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h3, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h39 | h39
                                  · rcases p19_3 (m.d 1 5) (by simp) with h40 | h40
                                    · rcases p19_3 (m.d 2 5) (by simp) with h41 | h41
                                      · linarith only [h41, h7, hlam]
                                      · rcases p19_3 (m.d 3 5) (by simp) with h43 | h43
                                        · linarith only [h43, h9, hlam]
                                        · rcases p19_3 (m.d 4 5) (by simp) with h45 | h45
                                          · linarith only [h10, h45, hlam]
                                          · linarith only [h13, h45, hlam]
                                    · linarith only [h40, h7, hlam]
                                  · linarith only [h39, h4, hlam]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  rcases p19_3 (m.d 0 5) (by simp) with h50 | h50
                                  · rcases p19_3 (m.d 1 5) (by simp) with h51 | h51
                                    · rcases p19_3 (m.d 2 5) (by simp) with h52 | h52
                                      · linarith only [h52, h7, hlam]
                                      · linarith only [h12, h52, hlam]
                                    · linarith only [h51, h9, hlam]
                                  · linarith only [h5, h50, hlam]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h10, h13, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h4, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h7, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h17, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h13, hlam, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h5, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h9, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h12, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h17, hlam, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h10, h6, h8, hc01, hc05, hlam, hphi, ht0b, ht5b, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h10, hlam, p19_0]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h10, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [h0, h10, h17, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                                · obtain ⟨p19_0, p19_1, p19_2, p19_3⟩ := h19c
                                  linarith only [hlam, p19_0]
                          · linarith only [h0, h11, h12, h6, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
                          · linarith only [h0, h11, h6, h74, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                              · rcases h5bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi4]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h81 | h81
                                  · rcases p78_3 (m.d 1 5) (by simp) with h82 | h82
                                    · linarith only [h3, h82, hlam]
                                    · linarith only [h7, h82, hlam]
                                  · linarith only [h4, h81, hlam]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h86 | h86
                                  · rcases p78_3 (m.d 1 5) (by simp) with h87 | h87
                                    · linarith only [h3, h87, hlam]
                                    · linarith only [h87, h9, hlam]
                                  · linarith only [h5, h86, hlam]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h91 | h91
                                  · rcases p78_3 (m.d 1 5) (by simp) with h92 | h92
                                    · linarith only [h3, h92, hlam]
                                    · linarith only [h10, h92, hlam]
                                  · linarith only [h91, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h3, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h98 | h98
                                  · rcases p78_3 (m.d 1 5) (by simp) with h99 | h99
                                    · rcases p78_3 (m.d 2 5) (by simp) with h100 | h100
                                      · linarith only [h100, h7, hlam]
                                      · rcases p78_3 (m.d 3 5) (by simp) with h102 | h102
                                        · linarith only [h102, h9, hlam]
                                        · linarith only [h102, h74, hlam]
                                    · linarith only [h7, h99, hlam]
                                  · linarith only [h4, h98, hlam]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h0, h10, h6, h74, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  rcases p78_3 (m.d 0 5) (by simp) with h108 | h108
                                  · rcases p78_3 (m.d 1 5) (by simp) with h109 | h109
                                    · rcases p78_3 (m.d 2 5) (by simp) with h110 | h110
                                      · linarith only [h110, h7, hlam]
                                      · linarith only [h110, h76, hlam]
                                    · linarith only [h10, h109, hlam]
                                  · linarith only [h108, h4, h76, hlam]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h4, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h7, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h74, hlam, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h0, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h5, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h9, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h0, h6, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h0, h6, h77, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p78_1]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h3, hc45, hlam, hphi, ht12, ht23, ht34, p78_1, u1ehi4]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h10, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h76, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [h77, hlam, p78_0]
                                · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                  linarith only [hlam, p78_0]
                              · linarith only [h0, h11, h7, h76, h77, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                              · linarith only [h0, h11, h131, h6, h76, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h0, h10, h11, h131, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h10, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                    · linarith only [h9, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                  · linarith only [h8, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                · linarith only [h7, hc25, hlam, hphi, ht12, u1ehi1]
              · linarith only [h6, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h1, h5, hc35, hlam, hphi, ht12, ht23, u1ehi2]
          · linarith only [h0, h4, hc25, hlam, hphi, ht12, u1ehi1]
        · linarith only [h3, hc15, hlam, hphi, u1ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA5_M_IR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h0, h3, h6, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h14, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h14, h16, h3, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h16, h3, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
              · linarith only [h5, h6, hc35, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
          · linarith only [h4, hc24, hlam, hphi, ht12, u1ehi1]
        · linarith only [h3, hc23, hlam, hphi, ht12, u1ehi1]
      · linarith only [h2, hc14, hlam, hphi, u1ehi0]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA5_M_IR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                            · linarith only [h18, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · linarith only [h18, h9, hlam]
                          · linarith only [h17, h7, hlam]
                        · linarith only [h16, h5, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                            · linarith only [h25, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · linarith only [h25, h9, hlam]
                          · linarith only [h24, h7, hlam]
                        · linarith only [h23, h5, hlam]
                    · linarith only [h14, hc15, hlam, hphi, p0_1, u1ehi1]
                  · linarith only [h13, h9, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
                · linarith only [h12, h9, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h35 | h35
    · rcases p0_3 (m.d 1 2) (by simp) with h36 | h36
      · linarith only [h36, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h38 | h38
        · linarith only [h38, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h40 | h40
          · linarith only [h40, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h42 | h42
            · linarith only [h42, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h44 | h44
              · rcases m.htr 0 1 3 (by decide) (by decide) with h45 | h45
                · rcases m.htr 0 1 4 (by decide) (by decide) with h46 | h46
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                        · linarith only [h36, h49, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                            · linarith only [h49, h52, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h55 | h55
                                · linarith only [h55, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                · linarith only [h42, h55, hlam]
                              · linarith only [h40, h54, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                            · linarith only [h49, h59, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                                · linarith only [h62, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                · linarith only [h42, h62, hlam]
                              · linarith only [h40, h61, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
                        · linarith only [h36, h66, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h69 | h69
                            · linarith only [h66, h69, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                              · linarith only [h48, h71, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                              · linarith only [h40, h71, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                            · linarith only [h66, h74, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                              · linarith only [h48, h76, hc01, hlam, hphi, p0_1, u0ehi2]
                              · linarith only [h40, h76, hlam]
                    · linarith only [h42, h47, hlam, p0_1]
                  · linarith only [h42, h46, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
                · linarith only [h45, hlam, p0_0]
              · linarith only [h42, h44, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
    · linarith only [h35, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h84 | h84
    · rcases p0_3 (m.d 1 2) (by simp) with h85 | h85
      · linarith only [h85, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h87 | h87
        · linarith only [h87, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
          · linarith only [h89, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h91 | h91
            · linarith only [h91, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h93 | h93
              · rcases m.htr 0 1 3 (by decide) (by decide) with h94 | h94
                · rcases m.htr 0 1 4 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
                          · linarith only [h85, h99, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                            · linarith only [h101, h99, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                              · linarith only [h103, h87, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                                · linarith only [h105, h98, h99, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                                  · linarith only [h107, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                  · linarith only [h107, h91, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                          · linarith only [h110, h85, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                            · linarith only [h110, h112, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                              · linarith only [h114, h87, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                                · linarith only [h114, h116, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
                                  · linarith only [h118, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                  · linarith only [h118, h91, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                          · linarith only [h122, h85, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                            · linarith only [h122, h124, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                              · linarith only [h126, h87, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                                · linarith only [h126, h128, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                                  · linarith only [h130, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                  · linarith only [h130, h91, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                          · linarith only [h133, h85, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h135 | h135
                            · linarith only [h133, h135, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h137 | h137
                              · linarith only [h137, h87, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h139 | h139
                                · linarith only [h137, h139, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h141 | h141
                                  · linarith only [h141, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                  · linarith only [h141, h91, hlam]
                    · linarith only [h96, hc15, hlam, hphi, p0_1, u1ehi3]
                  · linarith only [h95, hlam, p0_0]
                · linarith only [h91, h94, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
              · linarith only [h93, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h84, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h149 | h149
    · rcases p0_3 (m.d 1 2) (by simp) with h150 | h150
      · linarith only [h150, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h152 | h152
        · linarith only [h152, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h154 | h154
          · linarith only [h154, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h156 | h156
            · linarith only [h156, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h158 | h158
              · rcases m.htr 0 1 3 (by decide) (by decide) with h159 | h159
                · rcases m.htr 0 1 4 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h162 | h162
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h164 | h164
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h165 | h165
                            · linarith only [h150, h165, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h167 | h167
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h168 | h168
                                · linarith only [h152, h168, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h170 | h170
                                  · linarith only [h154, h170, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                                    · linarith only [h163, h165, h172, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                    · linarith only [h163, h165, h167, h172, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
                                · linarith only [h152, h175, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
                                  · linarith only [h154, h177, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
                                    · linarith only [h167, h179, hc23, hlam, hphi, ht12, u1ehi2]
                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h181 | h181
                                      · linarith only [h164, h165, h179, h181, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h183 | h183
                                        · linarith only [h164, h165, h183, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                        · rcases m.htr 3 4 5 (by decide) (by decide) with h185 | h185
                                          · linarith only [h162, h164, h165, h179, h183, h185, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                          · linarith only [h167, h185, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h188 | h188
                            · linarith only [h150, h188, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
                              · linarith only [h163, h164, h190, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                                · linarith only [h152, h192, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                                  · linarith only [h154, h194, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                                    · linarith only [h190, h196, hc23, hlam, hphi, ht12, u1ehi2]
                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                                      · linarith only [h163, h164, h198, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                                        · linarith only [h163, h164, h194, h196, h200, hc23, hc34, hlam, hphi]
                                        · linarith only [h163, h164, h200, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h203 | h203
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                            · linarith only [h150, h204, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h207 | h207
                                · linarith only [h152, h207, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h209 | h209
                                  · linarith only [h154, h209, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
                                      · linarith only [h163, h207, h212, hc23, hlam, hphi, ht12, u1ehi1]
                                      · linarith only [h163, h203, h212, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                    · linarith only [h163, h203, h211, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h163, h203, h206, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h217 | h217
                            · linarith only [h150, h217, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                                · linarith only [h152, h220, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h222 | h222
                                  · linarith only [h154, h222, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                                      · linarith only [h203, h219, h220, h225, hc23, hlam, hphi, ht12, u1ehi1]
                                      · linarith only [h163, h225, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                    · linarith only [h163, h219, h224, hc13, hlam, hphi, u1ehi1]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                                · linarith only [h152, h229, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                                  · linarith only [h154, h231, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                                    · linarith only [h163, h219, h233, hc23, hlam, hphi, ht12, u1ehi1]
                                    · linarith only [h163, h233, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h236 | h236
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
                            · linarith only [h150, h238, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
                              · linarith only [h162, h236, h240, hc12, hlam, hphi, ht01, u0ehi2]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                                · linarith only [h152, h242, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                                  · linarith only [h154, h244, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                                    · linarith only [h162, h236, h238, h246, hc01, hlam, hphi, p0_1, u0ehi2]
                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                                      · linarith only [h237, h238, h246, h248, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                                        · linarith only [h237, h238, h250, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                        · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                                          · linarith only [h237, h238, h240, h250, h252, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                          · linarith only [h162, h237, h238, h240, h252, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u0ehi2, u1ehi2]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
                            · linarith only [h150, h255, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h257 | h257
                              · linarith only [h162, h257, hc13, hlam, hphi, ht01, u0ehi2]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h259 | h259
                                · linarith only [h152, h259, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h261 | h261
                                  · linarith only [h154, h261, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                                    · linarith only [h162, h236, h237, h261, h263, hc01, hc23, hlam, hphi, ht12, p0_1, u0ehi2, u1ehi2]
                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h265 | h265
                                      · linarith only [h236, h237, h261, h265, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h267 | h267
                                        · linarith only [h236, h237, h261, h267, hc24, hlam, hphi, ht12, u1ehi2]
                                        · linarith only [h236, h237, h267, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                            · linarith only [h150, h271, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                              · linarith only [h152, h162, h273, hc01, hlam, hphi, p0_1, u0ehi2]
                              · linarith only [h236, h270, h273, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h276 | h276
                            · linarith only [h150, h276, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                              · linarith only [h152, h162, h278, hc01, hlam, hphi, p0_1, u0ehi2]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h280 | h280
                                · linarith only [h152, h280, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h282 | h282
                                  · linarith only [h154, h282, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h284 | h284
                                    · linarith only [h162, h284, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                                    · linarith only [h236, h284, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h161, hlam, p0_0]
                  · linarith only [h160, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
                · linarith only [h152, h159, hlam, p0_1]
              · linarith only [h154, h158, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h149, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_M_LI_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_M_LI_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_M_LI_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
            · linarith only [h7, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
                · linarith only [h16, h5, hlam]
                · linarith only [h16, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h15, hlam, p0_0]
            · linarith only [h14, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 1 5) (by simp) with h22 | h22
            · rcases m.htr 0 1 2 (by decide) (by decide) with h23 | h23
              · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 0 1 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h21, h25, hlam]
                  · linarith only [h25, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h24, h5, hlam, p0_1]
              · linarith only [h23, hlam, p0_0]
            · linarith only [h22, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h31 | h31
            · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h31, h35, hlam]
                    · linarith only [h35, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h21, h34, hlam, p0_1]
                · linarith only [h33, h5, hlam, p0_1]
              · linarith only [h32, hlam, p0_0]
            · linarith only [h31, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · rcases p0_3 (m.d 1 2) (by simp) with h44 | h44
      · rcases p0_3 (m.d 1 3) (by simp) with h45 | h45
        · linarith only [h45, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h47 | h47
          · rcases p0_3 (m.d 1 5) (by simp) with h48 | h48
            · rcases m.htr 0 1 2 (by decide) (by decide) with h49 | h49
              · linarith only [h44, h49, hlam]
              · linarith only [h49, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h48, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h44, h54, hlam]
              · linarith only [h54, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h53, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h58 | h58
        · linarith only [h58, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 1 5) (by simp) with h61 | h61
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · rcases m.htr 0 1 3 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
                  · linarith only [h60, h64, hlam]
                  · linarith only [h44, h64, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h63, hlam, p0_0]
              · linarith only [h44, h62, hlam, p0_1]
            · linarith only [h61, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h70 | h70
            · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
              · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h70, h74, hlam]
                    · linarith only [h74, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h60, h73, hlam, p0_1]
                · linarith only [h72, hlam, p0_0]
              · linarith only [h44, h71, hlam, p0_1]
            · linarith only [h70, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
    · linarith only [h43, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h82 | h82
    · rcases p0_3 (m.d 1 2) (by simp) with h83 | h83
      · rcases p0_3 (m.d 1 3) (by simp) with h84 | h84
        · rcases p0_3 (m.d 1 4) (by simp) with h85 | h85
          · linarith only [h85, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h87 | h87
            · rcases m.htr 0 1 2 (by decide) (by decide) with h88 | h88
              · linarith only [h83, h88, hlam]
              · linarith only [h88, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h87, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
          · linarith only [h92, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h94 | h94
            · rcases m.htr 0 1 2 (by decide) (by decide) with h95 | h95
              · linarith only [h83, h95, hlam]
              · linarith only [h84, h95, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h94, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
      · rcases p0_3 (m.d 1 3) (by simp) with h99 | h99
        · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
          · linarith only [h100, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h102 | h102
            · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
              · rcases m.htr 0 1 3 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h99, hlam]
                · linarith only [h104, h83, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h103, h83, hlam, p0_1]
            · linarith only [h102, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h109 | h109
          · linarith only [h109, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h111 | h111
            · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 1 3 (by decide) (by decide) with h113 | h113
                · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h111, h115, hlam]
                    · linarith only [h115, h99, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h114, hlam, p0_0]
                · linarith only [h113, h83, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h112, h83, hlam, p0_1]
            · linarith only [h111, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
    · linarith only [h82, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h126 | h126
    · rcases p0_3 (m.d 1 2) (by simp) with h127 | h127
      · rcases p0_3 (m.d 1 3) (by simp) with h128 | h128
        · linarith only [h128, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h130 | h130
          · rcases p0_3 (m.d 1 5) (by simp) with h131 | h131
            · rcases m.htr 0 1 2 (by decide) (by decide) with h132 | h132
              · linarith only [h132, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h126, h132, hlam]
            · linarith only [h131, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h136 | h136
            · rcases m.htr 0 1 2 (by decide) (by decide) with h137 | h137
              · linarith only [h137, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h126, h137, hlam]
            · linarith only [h136, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1, u5ehi1]
      · linarith only [h127, hlam, p0_0]
    · linarith only [h126, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h143 | h143
    · rcases p0_3 (m.d 1 2) (by simp) with h144 | h144
      · rcases p0_3 (m.d 1 3) (by simp) with h145 | h145
        · rcases p0_3 (m.d 1 4) (by simp) with h146 | h146
          · linarith only [h146, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h148 | h148
            · rcases m.htr 0 1 2 (by decide) (by decide) with h149 | h149
              · linarith only [h149, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h143, h149, hlam]
            · linarith only [h148, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1, u5ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h153 | h153
          · linarith only [h153, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h155 | h155
            · rcases m.htr 0 1 2 (by decide) (by decide) with h156 | h156
              · linarith only [h145, h156, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h143, h156, hlam]
            · linarith only [h155, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1, u5ehi1]
      · linarith only [h144, hlam, p0_0]
    · linarith only [h143, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h164 | h164
    · rcases p0_3 (m.d 1 2) (by simp) with h165 | h165
      · linarith only [h165, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h167 | h167
        · rcases p0_3 (m.d 1 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 1 5) (by simp) with h169 | h169
            · rcases m.htr 0 1 2 (by decide) (by decide) with h170 | h170
              · rcases m.htr 0 1 3 (by decide) (by decide) with h171 | h171
                · linarith only [h171, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h164, h171, hlam]
              · linarith only [h170, hc01, hlam, hphi, p0_1, u1elo2]
            · linarith only [h169, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2, u5ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h176 | h176
            · rcases m.htr 0 1 2 (by decide) (by decide) with h177 | h177
              · rcases m.htr 0 1 3 (by decide) (by decide) with h178 | h178
                · linarith only [h178, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h164, h178, hlam]
              · linarith only [h177, hc01, hlam, hphi, p0_1, u1elo2]
            · linarith only [h176, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2, u5ehi1]
        · linarith only [h167, hlam, p0_0]
    · linarith only [h164, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h186 | h186
    · rcases p0_3 (m.d 1 2) (by simp) with h187 | h187
      · rcases p0_3 (m.d 1 3) (by simp) with h188 | h188
        · rcases p0_3 (m.d 1 4) (by simp) with h189 | h189
          · linarith only [h189, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h191 | h191
            · rcases m.htr 0 1 2 (by decide) (by decide) with h192 | h192
              · linarith only [h187, h192, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h186, h192, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h186, h191, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
        · linarith only [h188, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h197 | h197
        · rcases p0_3 (m.d 1 4) (by simp) with h198 | h198
          · linarith only [h198, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h200 | h200
            · rcases m.htr 0 1 2 (by decide) (by decide) with h201 | h201
              · rcases m.htr 0 1 3 (by decide) (by decide) with h202 | h202
                · linarith only [h187, h202, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h186, h202, hlam]
              · linarith only [h187, h201, hc01, hlam, hphi, p0_1, u1elo2]
            · linarith only [h200, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2, u5ehi1]
        · linarith only [h197, hlam, p0_0]
    · linarith only [h186, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h211 | h211
    · rcases p0_3 (m.d 1 2) (by simp) with h212 | h212
      · linarith only [h212, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h214 | h214
        · rcases p0_3 (m.d 1 4) (by simp) with h215 | h215
          · rcases p0_3 (m.d 1 5) (by simp) with h216 | h216
            · rcases m.htr 0 1 2 (by decide) (by decide) with h217 | h217
              · rcases m.htr 0 1 3 (by decide) (by decide) with h218 | h218
                · linarith only [h214, h218, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                · linarith only [h211, h218, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h211, h217, hlam, p0_1]
            · linarith only [h211, h216, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
          · linarith only [h215, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h224 | h224
          · rcases p0_3 (m.d 1 5) (by simp) with h225 | h225
            · rcases m.htr 0 1 2 (by decide) (by decide) with h226 | h226
              · rcases m.htr 0 1 3 (by decide) (by decide) with h227 | h227
                · rcases m.htr 0 1 4 (by decide) (by decide) with h228 | h228
                  · linarith only [h228, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h211, h228, hlam]
                · linarith only [h214, h227, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h211, h226, hlam, p0_1]
            · linarith only [h225, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi1]
          · linarith only [h224, hlam, p0_0]
    · linarith only [h211, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h236 | h236
    · rcases p0_3 (m.d 1 2) (by simp) with h237 | h237
      · rcases p0_3 (m.d 1 3) (by simp) with h238 | h238
        · linarith only [h238, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h240 | h240
          · rcases p0_3 (m.d 1 5) (by simp) with h241 | h241
            · rcases m.htr 0 1 2 (by decide) (by decide) with h242 | h242
              · linarith only [h237, h242, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h236, h242, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h236, h241, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
          · linarith only [h240, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h247 | h247
        · linarith only [h247, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h249 | h249
          · rcases p0_3 (m.d 1 5) (by simp) with h250 | h250
            · rcases m.htr 0 1 2 (by decide) (by decide) with h251 | h251
              · rcases m.htr 0 1 3 (by decide) (by decide) with h252 | h252
                · rcases m.htr 0 1 4 (by decide) (by decide) with h253 | h253
                  · linarith only [h237, h253, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                  · linarith only [h236, h253, hlam]
                · linarith only [h252, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h236, h237, h251, hlam, p0_1]
            · linarith only [h250, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi1]
          · linarith only [h249, hlam, p0_0]
    · linarith only [h236, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h264 | h264
    · rcases p0_3 (m.d 1 2) (by simp) with h265 | h265
      · linarith only [h265, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h267 | h267
        · rcases p0_3 (m.d 1 4) (by simp) with h268 | h268
          · rcases p0_3 (m.d 1 5) (by simp) with h269 | h269
            · rcases m.htr 0 1 2 (by decide) (by decide) with h270 | h270
              · rcases m.htr 0 1 3 (by decide) (by decide) with h271 | h271
                · linarith only [h267, h271, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h264, h271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h264, h270, hlam, p0_1]
            · linarith only [h269, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h276 | h276
            · rcases m.htr 0 1 2 (by decide) (by decide) with h277 | h277
              · rcases m.htr 0 1 3 (by decide) (by decide) with h278 | h278
                · linarith only [h267, h278, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h264, h278, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h264, h277, hlam, p0_1]
            · linarith only [h276, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h283 | h283
          · rcases p0_3 (m.d 1 5) (by simp) with h284 | h284
            · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
              · rcases m.htr 0 1 3 (by decide) (by decide) with h286 | h286
                · rcases m.htr 0 1 4 (by decide) (by decide) with h287 | h287
                  · linarith only [h283, h287, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h264, h287, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h264, h267, h286, hlam, p0_1]
              · linarith only [h264, h285, hlam, p0_1]
            · linarith only [h284, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h293 | h293
            · rcases m.htr 0 1 2 (by decide) (by decide) with h294 | h294
              · rcases m.htr 0 1 3 (by decide) (by decide) with h295 | h295
                · rcases m.htr 0 1 4 (by decide) (by decide) with h296 | h296
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h297 | h297
                    · linarith only [h297, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h264, h297, hlam]
                  · linarith only [h283, h296, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h264, h267, h295, hlam, p0_1]
              · linarith only [h264, h294, hlam, p0_1]
            · linarith only [h293, hlam, p0_0]
    · linarith only [h264, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h305 | h305
    · rcases p0_3 (m.d 1 2) (by simp) with h306 | h306
      · rcases p0_3 (m.d 1 3) (by simp) with h307 | h307
        · linarith only [h307, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h309 | h309
          · rcases p0_3 (m.d 1 5) (by simp) with h310 | h310
            · rcases m.htr 0 1 2 (by decide) (by decide) with h311 | h311
              · linarith only [h306, h311, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h305, h311, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h310, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h315 | h315
            · rcases m.htr 0 1 2 (by decide) (by decide) with h316 | h316
              · linarith only [h306, h316, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h305, h316, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h315, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h320 | h320
        · linarith only [h320, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h322 | h322
          · rcases p0_3 (m.d 1 5) (by simp) with h323 | h323
            · rcases m.htr 0 1 2 (by decide) (by decide) with h324 | h324
              · rcases m.htr 0 1 3 (by decide) (by decide) with h325 | h325
                · rcases m.htr 0 1 4 (by decide) (by decide) with h326 | h326
                  · linarith only [h306, h322, h326, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h305, h306, h326, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h305, h325, hlam, p0_1]
              · linarith only [h305, h306, h324, hlam, p0_1]
            · linarith only [h323, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h332 | h332
            · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
              · rcases m.htr 0 1 3 (by decide) (by decide) with h334 | h334
                · rcases m.htr 0 1 4 (by decide) (by decide) with h335 | h335
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h336 | h336
                    · linarith only [h306, h336, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h305, h336, hlam]
                  · linarith only [h322, h335, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h305, h334, hlam, p0_1]
              · linarith only [h305, h306, h333, hlam, p0_1]
            · linarith only [h332, hlam, p0_0]
    · linarith only [h305, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h344 | h344
    · rcases p0_3 (m.d 1 2) (by simp) with h345 | h345
      · rcases p0_3 (m.d 1 3) (by simp) with h346 | h346
        · rcases p0_3 (m.d 1 4) (by simp) with h347 | h347
          · linarith only [h347, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h349 | h349
            · rcases m.htr 0 1 2 (by decide) (by decide) with h350 | h350
              · linarith only [h345, h350, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h344, h350, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h349, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h354 | h354
          · linarith only [h354, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h356 | h356
            · rcases m.htr 0 1 2 (by decide) (by decide) with h357 | h357
              · linarith only [h345, h346, h357, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h344, h346, h357, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h356, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h361 | h361
        · rcases p0_3 (m.d 1 4) (by simp) with h362 | h362
          · linarith only [h362, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h364 | h364
            · rcases m.htr 0 1 2 (by decide) (by decide) with h365 | h365
              · rcases m.htr 0 1 3 (by decide) (by decide) with h366 | h366
                · linarith only [h345, h361, h366, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h344, h345, h366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h344, h345, h365, hlam, p0_1]
            · linarith only [h364, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h371 | h371
          · linarith only [h371, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h373 | h373
            · rcases m.htr 0 1 2 (by decide) (by decide) with h374 | h374
              · rcases m.htr 0 1 3 (by decide) (by decide) with h375 | h375
                · rcases m.htr 0 1 4 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h377 | h377
                    · linarith only [h345, h377, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h344, h377, hlam]
                  · linarith only [h376, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h344, h361, h375, hlam, p0_1]
              · linarith only [h344, h345, h374, hlam, p0_1]
            · linarith only [h373, hlam, p0_0]
    · linarith only [h344, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_M_LR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_M_LR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_M_LR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h28 | h28
    · linarith only [h28, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h28, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA5_M_LR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
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
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h12, h14, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h17, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h12, h17, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                              · linarith only [h0, h12, h21, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h12, h23, h3, h6, h9, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                                  · linarith only [h0, h10, h25, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h2, h20, h25, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                              · linarith only [h0, h12, h20, h28, h3, h6, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                                · linarith only [h0, h12, h20, h3, h30, h6, h8, h9, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                                  · linarith only [h0, h12, h20, h32, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                                    · linarith only [h0, h12, h20, h3, h34, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                    · linarith only [h12, h34, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h11, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h10, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                      · linarith only [h0, h3, h39, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
                        · linarith only [h0, h3, h41, h9, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                                    · linarith only [h1, h43, h48, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h2, h44, h48, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h39, h44, h47, hlam]
                                · linarith only [h39, h44, h45, h46, hc45, hlam, hphi, u5elo3]
                              · linarith only [h0, h3, h45, h6, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                                  · linarith only [h0, h3, h44, h54, h56, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h3, h39, h56, h6, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h0, h3, h55, h7, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h43, h54, h9, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                              · linarith only [h0, h3, h43, h62, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h0, h3, h6, h62, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                              · linarith only [h0, h3, h43, h65, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h0, h3, h6, h65, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h8, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo4]
                · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
                · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                          · linarith only [h6, h70, h75, hlam, hphi, ht01, u0ehi9, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h77 | h77
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                              · linarith only [h0, h6, h70, h72, h78, hlam, hphi, u0ehi9, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                                · linarith only [h0, h73, h78, h80, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h6, h70, h80, hc23, hc34, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                              · linarith only [h6, h70, h72, h83, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h0, h4, h71, h72, h75, h77, h85, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h6, h70, h85, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h5, h72, h74, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h4, h72, h73, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                      · linarith only [h0, h3, h72, h90, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
                        · linarith only [h0, h3, h72, h92, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                          · linarith only [h6, h70, h94, hlam, hphi, ht01, u0ehi9, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                              · linarith only [h0, h3, h6, h70, h97, hlam, hphi, ht01, u0ehi9, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h100 | h100
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
                                    · rcases h1bigk with h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        rcases p102_3 (m.d 0 1) (by simp) with h104 | h104
                                        · rcases p102_3 (m.d 1 2) (by simp) with h105 | h105
                                          · linarith only [h105, hlam, p102_0]
                                          · rcases p102_3 (m.d 1 3) (by simp) with h107 | h107
                                            · linarith only [h1, h107, hlam]
                                            · linarith only [h107, h72, hlam]
                                        · linarith only [h104, hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        rcases p102_3 (m.d 0 1) (by simp) with h111 | h111
                                        · rcases p102_3 (m.d 1 2) (by simp) with h112 | h112
                                          · linarith only [h0, h112, hlam]
                                          · rcases p102_3 (m.d 1 3) (by simp) with h114 | h114
                                            · linarith only [h114, hlam, p102_0]
                                            · rcases p102_3 (m.d 1 4) (by simp) with h116 | h116
                                              · linarith only [h116, h2, hlam]
                                              · linarith only [h116, h94, hlam]
                                        · linarith only [h111, hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h96, hc45, hlam, hphi, ht01, ht0b, ht5b, p102_1, u1elo0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        rcases p102_3 (m.d 0 1) (by simp) with h121 | h121
                                        · rcases p102_3 (m.d 1 2) (by simp) with h122 | h122
                                          · linarith only [h0, h122, hlam]
                                          · rcases p102_3 (m.d 1 3) (by simp) with h124 | h124
                                            · linarith only [h1, h124, hlam]
                                            · rcases p102_3 (m.d 1 4) (by simp) with h126 | h126
                                              · linarith only [h126, h2, hlam]
                                              · linarith only [h126, h96, hlam]
                                        · linarith only [h121, hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h0, hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h72, hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h90, hlam, p102_1]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h92, hlam, p102_1]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h1, hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p102_1, u1elo0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h94, hlam, p102_1]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p102_1, u1elo0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h2, hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h0, h4, h90, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p102_1, u1elo0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h0, h4, h90, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p102_1, u1elo0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h0, h4, h90, h92, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p102_1, u1elo0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [hc01, hlam, hphi, p102_1, u1elo4]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h0, h4, h92, h97, h99, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p102_1, u1elo0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h0, h4, h72, h92, h97, h99, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p102_1, u1elo0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [h96, hlam, p102_0]
                                      · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                        linarith only [hlam, p102_0]
                                    · linarith only [h101, h6, h70, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                                  · linarith only [h100, h90, h96, hlam]
                                · linarith only [h6, h70, h99, hc23, hc34, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                              · linarith only [h0, h153, h4, h6, h71, h72, h94, h96, hc12, hc23, hlam, hphi, ht01, u0ehi7, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                                  · linarith only [h0, h156, h4, h72, h94, h96, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h153, h155, h156, hc35, hlam, hphi, u5elo4]
                                · linarith only [h155, h72, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h71, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo4]
                · linarith only [h70, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
            · linarith only [h4, h5, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h163 | h163
            · rcases m.htr 0 3 4 (by decide) (by decide) with h164 | h164
              · linarith only [h164, h3, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
                · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                      · linarith only [h166, h169, h3, h4, hlam, hphi, ht01, u0ehi9, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                          · linarith only [h164, h166, h172, hlam, hphi, ht01, u0ehi9, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h174 | h174
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                              · linarith only [h164, h166, h175, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                                · linarith only [h168, h169, h177, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h166, h175, h177, h3, h4, hc23, hc34, hlam, hphi]
                            · linarith only [h169, h171, h174, hc25, hlam, hphi, u5elo4]
                        · linarith only [h168, h171, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h168, h3, h4, hc12, hc24, hlam, hphi]
                  · linarith only [h167, h3, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h166, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
            · linarith only [h163, h3, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h186 | h186
          · rcases m.htr 0 2 5 (by decide) (by decide) with h187 | h187
            · rcases m.htr 0 3 4 (by decide) (by decide) with h188 | h188
              · rcases m.htr 0 3 5 (by decide) (by decide) with h189 | h189
                · rcases m.htr 0 4 5 (by decide) (by decide) with h190 | h190
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                    · linarith only [h186, h190, h191, h3, hlam, hphi, ht01, u0ehi9, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                                  · linarith only [h0, h193, h199, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h196, h199, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h186, h190, h198, h3, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                              · linarith only [h186, h190, h197, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                                  · linarith only [h193, h196, h206, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                                    · linarith only [h193, h196, h204, h208, hlam]
                                    · rcases h1bigk with h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h194, hc25, hlam, hphi, ht01, ht0b, ht5b, p210_1, u1elo0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h191, h194, h205, hc35, hlam, hphi, ht01, ht0b, ht5b, p210_1, u1elo0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        rcases p210_3 (m.d 0 1) (by simp) with h214 | h214
                                        · rcases p210_3 (m.d 1 2) (by simp) with h215 | h215
                                          · linarith only [h0, h215, hlam]
                                          · linarith only [h193, h215, hlam]
                                        · linarith only [h214, hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        rcases p210_3 (m.d 0 1) (by simp) with h219 | h219
                                        · rcases p210_3 (m.d 1 2) (by simp) with h220 | h220
                                          · linarith only [h0, h220, hlam]
                                          · linarith only [h194, h220, hlam]
                                        · linarith only [h219, hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h0, hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h191, hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h0, h193, h204, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p210_1, u1elo0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h1, h191, hc15, hlam, hphi, ht01, ht0b, ht5b, p210_1, u1elo0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h1, hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p210_1, u1elo0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h1, h193, h204, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p210_1, u1elo0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h1, h194, h204, h206, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p210_1, u1elo0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h2, hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h193, hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h195, hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h196, hlam, p210_1]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [hc01, hlam, hphi, p210_1, u1elo4]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h194, hlam, p210_0]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h191, h194, hlam, p210_1]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [h193, h204, hc34, hlam, hphi, ht45, p210_1, u5elo1]
                                      · obtain ⟨p210_0, p210_1, p210_2, p210_3⟩ := h210c
                                        linarith only [hlam, p210_0]
                                · linarith only [h186, h190, h193, h196, h204, h205, h3, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h186, h190, h193, h196, h204, h3, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h188, h191, h193, h195, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h193, h194, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h186, h193, h3, hc12, hc23, hlam, hphi]
                  · linarith only [h190, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo4]
                · linarith only [h186, h189, h3, hc24, hlam, hphi, ht45, u5elo3]
              · linarith only [h186, h188, h3, hlam]
            · linarith only [h186, h187, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h253 | h253
            · rcases m.htr 0 3 4 (by decide) (by decide) with h254 | h254
              · rcases m.htr 0 3 5 (by decide) (by decide) with h255 | h255
                · rcases m.htr 0 4 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h257 | h257
                    · linarith only [h0, h257, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h259 | h259
                      · linarith only [h186, h253, h259, hlam, hphi, ht01, u0ehi9, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h261 | h261
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h262 | h262
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h265 | h265
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h266 | h266
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h267 | h267
                                    · linarith only [h1, h262, h267, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h1, h262, h263, h267, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h1, h186, h253, h262, h263, h266, hlam, hphi, ht01, u0ehi9, u1elo0]
                                · linarith only [h186, h253, h264, h265, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                              · linarith only [h253, h264, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                            · linarith only [h259, h261, h263, hc25, hlam, hphi, u5elo4]
                          · linarith only [h254, h257, h261, h262, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h253, h261, h3, hc12, hc23, hlam, hphi]
                  · linarith only [h186, h253, h256, hc25, hlam, hphi, u5elo4]
                · linarith only [h254, h255, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h278 | h278
                · rcases m.htr 0 4 5 (by decide) (by decide) with h279 | h279
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h280 | h280
                    · linarith only [h253, h280, h3, hlam, hphi, ht01, u0ehi9, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h282 | h282
                      · linarith only [h186, h253, h282, hlam, hphi, ht01, u0ehi9, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h284 | h284
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h285 | h285
                          · linarith only [h1, h253, h254, h285, h3, hlam, hphi, ht01, u0ehi9, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h287 | h287
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h288 | h288
                              · linarith only [h253, h254, h288, h3, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                              · linarith only [h253, h288, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                            · linarith only [h2, h279, h280, h284, h285, h287, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h253, h284, h3, hc12, hc23, hlam, hphi]
                  · linarith only [h279, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo4]
                · linarith only [h253, h278, h3, hc25, hlam, hphi, u5elo3]
            · linarith only [h253, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
      · linarith only [h2, hlam, hphi, ht01, u0ehi5, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem n7l_sAA5_M_LR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                · linarith only [h3, h4, h5, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h3, h4, h5, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                  · rcases h1bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12_1, u1elo0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12_1, u1elo0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      rcases p12_3 (m.d 0 1) (by simp) with h16 | h16
                      · rcases p12_3 (m.d 1 2) (by simp) with h17 | h17
                        · linarith only [h0, h17, hlam]
                        · linarith only [h17, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12_1, u1elo0]
                      · linarith only [h16, hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12_1, u1elo0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h0, hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12_1, u1elo1]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h3, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p12_1, u1elo0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h5, hlam, p12_1]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h1, hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h4, hlam, p12_1]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p12_1, u1elo0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h8, hlam, p12_1]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h2, hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p12_1, u1elo0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h7, hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h10, hlam, p12_1]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h3, hlam, p12_0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12_1, u1elo0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h3, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12_1, u1elo0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p12_1, u1elo0]
                    · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                      linarith only [hlam, p12_0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                · linarith only [h1, h42, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                  · linarith only [h2, h44, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                  · rcases h1bigk with h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p46_1, u1elo0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      rcases p46_3 (m.d 0 1) (by simp) with h49 | h49
                      · rcases p46_3 (m.d 1 2) (by simp) with h50 | h50
                        · linarith only [h0, h50, hlam]
                        · linarith only [h4, h50, hlam]
                      · linarith only [h49, hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      rcases p46_3 (m.d 0 1) (by simp) with h54 | h54
                      · rcases p46_3 (m.d 1 2) (by simp) with h55 | h55
                        · linarith only [h0, h55, hlam]
                        · linarith only [h4, h55, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p46_1, u1elo0]
                      · linarith only [h54, hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [hlam, hphi, ht01, ht0b, ht5b, p46_1, u1elo0, u5ehi1]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h0, hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p46_1, u1elo0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p46_1, u1elo0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h5, hlam, p46_1]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h1, hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h4, hlam, p46_1]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h7, hlam, p46_1]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h42, hlam, p46_1]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h2, hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p46_1, u1elo0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p46_1, u1elo0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h44, hlam, p46_1]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h3, hlam, p46_0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p46_1, u1elo0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p46_1, u1elo0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p46_1, u1elo0]
                    · obtain ⟨p46_0, p46_1, p46_2, p46_3⟩ := h46c
                      linarith only [hlam, p46_0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
            · linarith only [h0, h80, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
              · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                · linarith only [h1, h83, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                  · linarith only [h2, h85, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                  · rcases h1bigk with h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      rcases p87_3 (m.d 0 1) (by simp) with h89 | h89
                      · rcases p87_3 (m.d 1 2) (by simp) with h90 | h90
                        · linarith only [h90, hlam, p87_0]
                        · rcases p87_3 (m.d 1 3) (by simp) with h92 | h92
                          · linarith only [h1, h92, hlam]
                          · linarith only [h4, h92, hlam]
                      · linarith only [h89, hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h82, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p87_1, u1elo0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      rcases p87_3 (m.d 0 1) (by simp) with h97 | h97
                      · rcases p87_3 (m.d 1 2) (by simp) with h98 | h98
                        · linarith only [h0, h98, hlam]
                        · rcases p87_3 (m.d 1 3) (by simp) with h100 | h100
                          · linarith only [h1, h100, hlam]
                          · linarith only [h100, h82, hlam]
                      · linarith only [h97, hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [hlam, hphi, ht01, ht0b, ht5b, p87_1, u1elo0, u5ehi1]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h0, hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h4, hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p87_1, u1elo0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h80, hlam, p87_1]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h1, hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h83, hc12, hc35, hlam, hphi, ht23, p87_1]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h3, h83, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p87_1, u1elo0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h83, hlam, p87_1]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h2, hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p87_1, u1elo0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h82, hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h85, hlam, p87_1]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h3, hlam, p87_0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p87_1, u1elo0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p87_1, u1elo0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p87_1, u1elo0]
                    · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                      linarith only [hlam, p87_0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                · linarith only [h1, h125, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
                  · linarith only [h127, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                  · rcases h1bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      rcases p129_3 (m.d 0 1) (by simp) with h131 | h131
                      · rcases p129_3 (m.d 1 2) (by simp) with h132 | h132
                        · linarith only [h132, hlam, p129_0]
                        · rcases p129_3 (m.d 1 3) (by simp) with h134 | h134
                          · linarith only [h1, h134, hlam]
                          · linarith only [h134, h4, hlam]
                      · linarith only [h131, hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      rcases p129_3 (m.d 0 1) (by simp) with h138 | h138
                      · rcases p129_3 (m.d 1 2) (by simp) with h139 | h139
                        · linarith only [h0, h139, hlam]
                        · rcases p129_3 (m.d 1 3) (by simp) with h141 | h141
                          · linarith only [h141, hlam, p129_0]
                          · rcases p129_3 (m.d 1 4) (by simp) with h143 | h143
                            · linarith only [h143, h2, hlam]
                            · linarith only [h143, h82, hlam]
                      · linarith only [h138, hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      rcases p129_3 (m.d 0 1) (by simp) with h147 | h147
                      · rcases p129_3 (m.d 1 2) (by simp) with h148 | h148
                        · linarith only [h0, h148, hlam]
                        · rcases p129_3 (m.d 1 3) (by simp) with h150 | h150
                          · linarith only [h1, h150, hlam]
                          · rcases p129_3 (m.d 1 4) (by simp) with h152 | h152
                            · linarith only [h152, hlam, p129_0]
                            · rcases p129_3 (m.d 1 5) (by simp) with h154 | h154
                              · linarith only [h154, h3, hlam]
                              · linarith only [h127, h154, hlam]
                      · linarith only [h147, hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [hlam, hphi, ht01, ht0b, ht5b, p129_1, u1elo0, u5ehi1]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h0, hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h4, hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h0, h82, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p129_1, u1elo0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h80, hlam, p129_1]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h1, hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h82, hc12, hc34, hlam, hphi, ht23, p129_1]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h82, hlam, p129_1]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h125, hlam, p129_1]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h2, hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h127, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p129_1, u1elo0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h127, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p129_1, u1elo0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h127, hlam, p129_1]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h3, hlam, p129_0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p129_1, u1elo0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h3, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p129_1, u1elo0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p129_1, u1elo0]
                    · obtain ⟨p129_0, p129_1, p129_2, p129_3⟩ := h129c
                      linarith only [hlam, p129_0]
        · linarith only [h3, hlam, hphi, ht01, u0ehi5, u1elo4]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi6, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

end R2N4
