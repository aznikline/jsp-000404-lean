import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3846000 in
theorem n8l_sAA8_H_I_H_I (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h1bigk := hb1.1
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 1 6) (by simp) with h8 | h8
              · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
                · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h5, hlam]
                  · linarith only [h10, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h9, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h14 | h14
                · rcases m.htr 0 1 3 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h5, hlam]
                  · linarith only [h15, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h14, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h19 | h19
              · rcases m.htr 0 1 2 (by decide) (by decide) with h20 | h20
                · rcases m.htr 0 1 3 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, h5, hlam]
                  · linarith only [h21, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h20, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
                  · linarith only [h26, h5, hlam]
                  · linarith only [h26, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h25, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h30 | h30
            · rcases p0_3 (m.d 1 6) (by simp) with h31 | h31
              · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
                · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                  · linarith only [h33, h5, hlam]
                  · linarith only [h33, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h32, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h37 | h37
                · rcases m.htr 0 1 3 (by decide) (by decide) with h38 | h38
                  · linarith only [h38, h5, hlam]
                  · linarith only [h38, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h37, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h42 | h42
              · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
                · rcases m.htr 0 1 3 (by decide) (by decide) with h44 | h44
                  · linarith only [h44, h5, hlam]
                  · linarith only [h44, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h43, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
                · rcases m.htr 0 1 3 (by decide) (by decide) with h49 | h49
                  · linarith only [h49, h5, hlam]
                  · linarith only [h49, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h48, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
          · rcases p0_3 (m.d 1 5) (by simp) with h54 | h54
            · rcases p0_3 (m.d 1 6) (by simp) with h55 | h55
              · rcases m.htr 0 1 2 (by decide) (by decide) with h56 | h56
                · rcases m.htr 0 1 3 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h58 | h58
                    · linarith only [h53, h58, hlam]
                    · linarith only [h58, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h5, h57, hlam, p0_1]
                · linarith only [h56, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 3 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h65 | h65
                    · linarith only [h53, h65, hlam]
                    · linarith only [h65, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h5, h64, hlam, p0_1]
                · linarith only [h63, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h70 | h70
              · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
                · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                    · linarith only [h53, h73, hlam]
                    · linarith only [h73, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h5, h72, hlam, p0_1]
                · linarith only [h71, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h78 | h78
                · rcases m.htr 0 1 3 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h80 | h80
                    · linarith only [h53, h80, hlam]
                    · linarith only [h80, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h5, h79, hlam, p0_1]
                · linarith only [h78, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h85 | h85
            · rcases p0_3 (m.d 1 6) (by simp) with h86 | h86
              · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
                · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
                      · linarith only [h85, h90, hlam]
                      · linarith only [h90, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h53, h89, hlam, p0_1]
                  · linarith only [h5, h88, hlam, p0_1]
                · linarith only [h87, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h96 | h96
                · rcases m.htr 0 1 3 (by decide) (by decide) with h97 | h97
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h99 | h99
                      · linarith only [h85, h99, hlam]
                      · linarith only [h99, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h53, h98, hlam, p0_1]
                  · linarith only [h5, h97, hlam, p0_1]
                · linarith only [h96, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h105 | h105
              · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
                · rcases m.htr 0 1 3 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h110 | h110
                        · linarith only [h105, h110, hlam]
                        · linarith only [h110, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h109, h85, hlam, p0_1]
                    · linarith only [h108, h53, hlam, p0_1]
                  · linarith only [h107, h5, hlam, p0_1]
                · linarith only [h106, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h117 | h117
                · rcases m.htr 0 1 3 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h120 | h120
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h121 | h121
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                          · linarith only [h122, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h122, h5, hlam]
                        · linarith only [h105, h121, hlam, p0_1]
                      · linarith only [h120, h85, hlam, p0_1]
                    · linarith only [h119, h53, hlam, p0_1]
                  · linarith only [h118, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h117, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h131 | h131
    · rcases p0_3 (m.d 1 2) (by simp) with h132 | h132
      · rcases p0_3 (m.d 1 3) (by simp) with h133 | h133
        · linarith only [h133, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h135 | h135
          · rcases p0_3 (m.d 1 5) (by simp) with h136 | h136
            · rcases p0_3 (m.d 1 6) (by simp) with h137 | h137
              · rcases m.htr 0 1 2 (by decide) (by decide) with h138 | h138
                · linarith only [h132, h138, hlam]
                · linarith only [h138, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
                · linarith only [h132, h141, hlam]
                · linarith only [h141, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h144 | h144
              · rcases m.htr 0 1 2 (by decide) (by decide) with h145 | h145
                · linarith only [h132, h145, hlam]
                · linarith only [h145, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h148 | h148
                · linarith only [h132, h148, hlam]
                · linarith only [h148, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h151 | h151
            · rcases p0_3 (m.d 1 6) (by simp) with h152 | h152
              · rcases m.htr 0 1 2 (by decide) (by decide) with h153 | h153
                · linarith only [h132, h153, hlam]
                · linarith only [h153, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h156 | h156
                · linarith only [h132, h156, hlam]
                · linarith only [h156, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h159 | h159
              · rcases m.htr 0 1 2 (by decide) (by decide) with h160 | h160
                · linarith only [h132, h160, hlam]
                · linarith only [h160, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h163 | h163
                · linarith only [h132, h163, hlam]
                · linarith only [h163, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 1 5) (by simp) with h169 | h169
            · rcases p0_3 (m.d 1 6) (by simp) with h170 | h170
              · rcases m.htr 0 1 2 (by decide) (by decide) with h171 | h171
                · rcases m.htr 0 1 3 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h173 | h173
                    · linarith only [h168, h173, hlam]
                    · linarith only [h132, h173, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h172, hlam, p0_0]
                · linarith only [h132, h171, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h178 | h178
                · rcases m.htr 0 1 3 (by decide) (by decide) with h179 | h179
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h180 | h180
                    · linarith only [h168, h180, hlam]
                    · linarith only [h132, h180, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h179, hlam, p0_0]
                · linarith only [h132, h178, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h185 | h185
              · rcases m.htr 0 1 2 (by decide) (by decide) with h186 | h186
                · rcases m.htr 0 1 3 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h188 | h188
                    · linarith only [h168, h188, hlam]
                    · linarith only [h132, h188, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h187, hlam, p0_0]
                · linarith only [h132, h186, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h193 | h193
                · rcases m.htr 0 1 3 (by decide) (by decide) with h194 | h194
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h195 | h195
                    · linarith only [h168, h195, hlam]
                    · linarith only [h132, h195, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h194, hlam, p0_0]
                · linarith only [h132, h193, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h200 | h200
            · rcases p0_3 (m.d 1 6) (by simp) with h201 | h201
              · rcases m.htr 0 1 2 (by decide) (by decide) with h202 | h202
                · rcases m.htr 0 1 3 (by decide) (by decide) with h203 | h203
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h204 | h204
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h205 | h205
                      · linarith only [h200, h205, hlam]
                      · linarith only [h132, h205, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h168, h204, hlam, p0_1]
                  · linarith only [h203, hlam, p0_0]
                · linarith only [h132, h202, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h211 | h211
                · rcases m.htr 0 1 3 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h214 | h214
                      · linarith only [h200, h214, hlam]
                      · linarith only [h132, h214, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h168, h213, hlam, p0_1]
                  · linarith only [h212, hlam, p0_0]
                · linarith only [h132, h211, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h220 | h220
              · rcases m.htr 0 1 2 (by decide) (by decide) with h221 | h221
                · rcases m.htr 0 1 3 (by decide) (by decide) with h222 | h222
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h224 | h224
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h225 | h225
                        · linarith only [h220, h225, hlam]
                        · linarith only [h132, h225, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h200, h224, hlam, p0_1]
                    · linarith only [h168, h223, hlam, p0_1]
                  · linarith only [h222, hlam, p0_0]
                · linarith only [h132, h221, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h232 | h232
                · rcases m.htr 0 1 3 (by decide) (by decide) with h233 | h233
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h234 | h234
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h235 | h235
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h236 | h236
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                          · linarith only [h132, h237, hlam]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
                            · linarith only [h237, h239, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
                              · linarith only [h237, h241, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h243 | h243
                                · linarith only [h237, h243, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h245 | h245
                                  · linarith only [h245, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h168, h245, hlam]
                        · linarith only [h220, h236, hlam, p0_1]
                      · linarith only [h200, h235, hlam, p0_1]
                    · linarith only [h234, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h233, hlam, p0_0]
                · linarith only [h232, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h131, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h254 | h254
    · rcases p0_3 (m.d 1 2) (by simp) with h255 | h255
      · rcases p0_3 (m.d 1 3) (by simp) with h256 | h256
        · rcases p0_3 (m.d 1 4) (by simp) with h257 | h257
          · linarith only [h257, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h259 | h259
            · rcases p0_3 (m.d 1 6) (by simp) with h260 | h260
              · rcases m.htr 0 1 2 (by decide) (by decide) with h261 | h261
                · linarith only [h255, h261, hlam]
                · linarith only [h261, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h264 | h264
                · linarith only [h255, h264, hlam]
                · linarith only [h264, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h267 | h267
              · rcases m.htr 0 1 2 (by decide) (by decide) with h268 | h268
                · linarith only [h255, h268, hlam]
                · linarith only [h268, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h271 | h271
                · linarith only [h255, h271, hlam]
                · linarith only [h271, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h274 | h274
          · linarith only [h274, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h276 | h276
            · rcases p0_3 (m.d 1 6) (by simp) with h277 | h277
              · rcases m.htr 0 1 2 (by decide) (by decide) with h278 | h278
                · linarith only [h255, h278, hlam]
                · linarith only [h256, h278, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h281 | h281
                · linarith only [h255, h281, hlam]
                · linarith only [h256, h281, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h284 | h284
              · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
                · linarith only [h255, h285, hlam]
                · linarith only [h256, h285, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h288 | h288
                · linarith only [h255, h288, hlam]
                · linarith only [h256, h288, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h291 | h291
        · rcases p0_3 (m.d 1 4) (by simp) with h292 | h292
          · linarith only [h292, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h294 | h294
            · rcases p0_3 (m.d 1 6) (by simp) with h295 | h295
              · rcases m.htr 0 1 2 (by decide) (by decide) with h296 | h296
                · rcases m.htr 0 1 3 (by decide) (by decide) with h297 | h297
                  · linarith only [h291, h297, hlam]
                  · linarith only [h255, h297, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h255, h296, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h301 | h301
                · rcases m.htr 0 1 3 (by decide) (by decide) with h302 | h302
                  · linarith only [h291, h302, hlam]
                  · linarith only [h255, h302, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h255, h301, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h306 | h306
              · rcases m.htr 0 1 2 (by decide) (by decide) with h307 | h307
                · rcases m.htr 0 1 3 (by decide) (by decide) with h308 | h308
                  · linarith only [h291, h308, hlam]
                  · linarith only [h255, h308, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h255, h307, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h312 | h312
                · rcases m.htr 0 1 3 (by decide) (by decide) with h313 | h313
                  · linarith only [h291, h313, hlam]
                  · linarith only [h255, h313, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h255, h312, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h317 | h317
          · linarith only [h317, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h319 | h319
            · rcases p0_3 (m.d 1 6) (by simp) with h320 | h320
              · rcases m.htr 0 1 2 (by decide) (by decide) with h321 | h321
                · rcases m.htr 0 1 3 (by decide) (by decide) with h322 | h322
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h323 | h323
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h324 | h324
                      · linarith only [h319, h324, hlam]
                      · linarith only [h255, h324, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h323, hlam, p0_0]
                  · linarith only [h291, h322, hlam, p0_1]
                · linarith only [h255, h321, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h330 | h330
                · rcases m.htr 0 1 3 (by decide) (by decide) with h331 | h331
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h332 | h332
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h333 | h333
                      · linarith only [h319, h333, hlam]
                      · linarith only [h255, h333, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h332, hlam, p0_0]
                  · linarith only [h291, h331, hlam, p0_1]
                · linarith only [h255, h330, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h339 | h339
              · rcases m.htr 0 1 2 (by decide) (by decide) with h340 | h340
                · rcases m.htr 0 1 3 (by decide) (by decide) with h341 | h341
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h342 | h342
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h343 | h343
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h344 | h344
                        · linarith only [h339, h344, hlam]
                        · linarith only [h255, h344, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h319, h343, hlam, p0_1]
                    · linarith only [h342, hlam, p0_0]
                  · linarith only [h291, h341, hlam, p0_1]
                · linarith only [h255, h340, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h351 | h351
                · rcases m.htr 0 1 3 (by decide) (by decide) with h352 | h352
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h353 | h353
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h354 | h354
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h355 | h355
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h356 | h356
                          · linarith only [h255, h356, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h358 | h358
                            · linarith only [h255, h358, hlam]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                              · linarith only [h291, h356, h360, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h362 | h362
                                · linarith only [h291, h356, h362, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
                                  · linarith only [h291, h364, hlam]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h366 | h366
                                    · linarith only [h364, h366, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h368 | h368
                                      · linarith only [h364, h368, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                                        · linarith only [h370, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                        · linarith only [h319, h370, hlam]
                        · linarith only [h339, h355, hlam, p0_1]
                      · linarith only [h354, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h353, hlam, p0_0]
                  · linarith only [h352, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h255, h351, hlam, p0_1]
    · linarith only [h254, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h379 | h379
    · rcases p0_3 (m.d 1 2) (by simp) with h380 | h380
      · rcases p0_3 (m.d 1 3) (by simp) with h381 | h381
        · rcases p0_3 (m.d 1 4) (by simp) with h382 | h382
          · rcases p0_3 (m.d 1 5) (by simp) with h383 | h383
            · linarith only [h383, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h385 | h385
              · rcases m.htr 0 1 2 (by decide) (by decide) with h386 | h386
                · linarith only [h380, h386, hlam]
                · linarith only [h386, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h389 | h389
                · linarith only [h380, h389, hlam]
                · linarith only [h389, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h392 | h392
            · linarith only [h392, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h394 | h394
              · rcases m.htr 0 1 2 (by decide) (by decide) with h395 | h395
                · linarith only [h380, h395, hlam]
                · linarith only [h382, h395, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h398 | h398
                · linarith only [h380, h398, hlam]
                · linarith only [h382, h398, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h401 | h401
          · rcases p0_3 (m.d 1 5) (by simp) with h402 | h402
            · linarith only [h402, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h404 | h404
              · rcases m.htr 0 1 2 (by decide) (by decide) with h405 | h405
                · linarith only [h380, h405, hlam]
                · linarith only [h381, h405, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h408 | h408
                · linarith only [h380, h408, hlam]
                · linarith only [h381, h408, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h411 | h411
            · linarith only [h411, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h413 | h413
              · rcases m.htr 0 1 2 (by decide) (by decide) with h414 | h414
                · linarith only [h380, h414, hlam]
                · linarith only [h381, h414, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h417 | h417
                · linarith only [h380, h417, hlam]
                · linarith only [h381, h417, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h420 | h420
        · rcases p0_3 (m.d 1 4) (by simp) with h421 | h421
          · rcases p0_3 (m.d 1 5) (by simp) with h422 | h422
            · linarith only [h422, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h424 | h424
              · rcases m.htr 0 1 2 (by decide) (by decide) with h425 | h425
                · rcases m.htr 0 1 3 (by decide) (by decide) with h426 | h426
                  · linarith only [h420, h426, hlam]
                  · linarith only [h380, h426, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h380, h425, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h430 | h430
                · rcases m.htr 0 1 3 (by decide) (by decide) with h431 | h431
                  · linarith only [h420, h431, hlam]
                  · linarith only [h380, h431, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h380, h430, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h435 | h435
            · linarith only [h435, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h437 | h437
              · rcases m.htr 0 1 2 (by decide) (by decide) with h438 | h438
                · rcases m.htr 0 1 3 (by decide) (by decide) with h439 | h439
                  · linarith only [h420, h439, hlam]
                  · linarith only [h380, h439, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h380, h438, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h443 | h443
                · rcases m.htr 0 1 3 (by decide) (by decide) with h444 | h444
                  · linarith only [h420, h444, hlam]
                  · linarith only [h380, h444, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h380, h443, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h448 | h448
          · rcases p0_3 (m.d 1 5) (by simp) with h449 | h449
            · linarith only [h449, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h451 | h451
              · rcases m.htr 0 1 2 (by decide) (by decide) with h452 | h452
                · rcases m.htr 0 1 3 (by decide) (by decide) with h453 | h453
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h454 | h454
                    · linarith only [h448, h454, hlam]
                    · linarith only [h380, h454, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h420, h453, hlam, p0_1]
                · linarith only [h380, h452, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h459 | h459
                · rcases m.htr 0 1 3 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h461 | h461
                    · linarith only [h448, h461, hlam]
                    · linarith only [h380, h461, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h420, h460, hlam, p0_1]
                · linarith only [h380, h459, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h466 | h466
            · linarith only [h466, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h468 | h468
              · rcases m.htr 0 1 2 (by decide) (by decide) with h469 | h469
                · rcases m.htr 0 1 3 (by decide) (by decide) with h470 | h470
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h471 | h471
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h472 | h472
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h473 | h473
                        · linarith only [h468, h473, hlam]
                        · linarith only [h380, h473, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h472, hlam, p0_0]
                    · linarith only [h448, h471, hlam, p0_1]
                  · linarith only [h420, h470, hlam, p0_1]
                · linarith only [h380, h469, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h480 | h480
                · rcases m.htr 0 1 3 (by decide) (by decide) with h481 | h481
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h482 | h482
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h483 | h483
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h484 | h484
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h485 | h485
                          · linarith only [h380, h485, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h487 | h487
                            · linarith only [h420, h485, h487, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h489 | h489
                              · linarith only [h380, h489, hlam]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h491 | h491
                                · linarith only [h420, h485, h491, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                                  · linarith only [h420, h493, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                                    · linarith only [h420, h495, hlam]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h497 | h497
                                      · linarith only [h448, h493, h497, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h499 | h499
                                        · linarith only [h448, h499, hlam]
                                        · rcases m.htr 1 4 6 (by decide) (by decide) with h501 | h501
                                          · linarith only [h499, h501, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                          · rcases m.htr 1 5 6 (by decide) (by decide) with h503 | h503
                                            · linarith only [h503, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                                            · linarith only [h468, h503, hlam]
                        · linarith only [h484, hc15, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h483, hlam, p0_0]
                    · linarith only [h482, hc14, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h380, h481, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h380, h480, hlam, p0_1]
    · linarith only [h379, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h512 | h512
    · rcases p0_3 (m.d 1 2) (by simp) with h513 | h513
      · rcases p0_3 (m.d 1 3) (by simp) with h514 | h514
        · rcases p0_3 (m.d 1 4) (by simp) with h515 | h515
          · rcases p0_3 (m.d 1 5) (by simp) with h516 | h516
            · rcases p0_3 (m.d 1 6) (by simp) with h517 | h517
              · linarith only [h517, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h519 | h519
                · linarith only [h513, h519, hlam]
                · linarith only [h519, hc12, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h522 | h522
              · linarith only [h522, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h524 | h524
                · linarith only [h513, h524, hlam]
                · linarith only [h516, h524, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h527 | h527
            · rcases p0_3 (m.d 1 6) (by simp) with h528 | h528
              · linarith only [h528, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h530 | h530
                · linarith only [h513, h530, hlam]
                · linarith only [h515, h530, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h533 | h533
              · linarith only [h533, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h535 | h535
                · linarith only [h513, h535, hlam]
                · linarith only [h515, h535, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h538 | h538
          · rcases p0_3 (m.d 1 5) (by simp) with h539 | h539
            · rcases p0_3 (m.d 1 6) (by simp) with h540 | h540
              · linarith only [h540, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h542 | h542
                · linarith only [h513, h542, hlam]
                · linarith only [h514, h542, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h545 | h545
              · linarith only [h545, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h547 | h547
                · linarith only [h513, h547, hlam]
                · linarith only [h514, h547, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h550 | h550
            · rcases p0_3 (m.d 1 6) (by simp) with h551 | h551
              · linarith only [h551, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h553 | h553
                · linarith only [h513, h553, hlam]
                · linarith only [h514, h553, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h556 | h556
              · linarith only [h556, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h558 | h558
                · linarith only [h513, h558, hlam]
                · linarith only [h514, h558, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h561 | h561
        · rcases p0_3 (m.d 1 4) (by simp) with h562 | h562
          · rcases p0_3 (m.d 1 5) (by simp) with h563 | h563
            · rcases p0_3 (m.d 1 6) (by simp) with h564 | h564
              · linarith only [h564, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h566 | h566
                · rcases m.htr 0 1 3 (by decide) (by decide) with h567 | h567
                  · linarith only [h561, h567, hlam]
                  · linarith only [h513, h567, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h513, h566, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h571 | h571
              · linarith only [h571, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h573 | h573
                · rcases m.htr 0 1 3 (by decide) (by decide) with h574 | h574
                  · linarith only [h561, h574, hlam]
                  · linarith only [h513, h574, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h513, h573, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h578 | h578
            · rcases p0_3 (m.d 1 6) (by simp) with h579 | h579
              · linarith only [h579, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h581 | h581
                · rcases m.htr 0 1 3 (by decide) (by decide) with h582 | h582
                  · linarith only [h561, h582, hlam]
                  · linarith only [h513, h582, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h513, h581, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h586 | h586
              · linarith only [h586, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h588 | h588
                · rcases m.htr 0 1 3 (by decide) (by decide) with h589 | h589
                  · linarith only [h561, h589, hlam]
                  · linarith only [h513, h589, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h513, h588, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h593 | h593
          · rcases p0_3 (m.d 1 5) (by simp) with h594 | h594
            · rcases p0_3 (m.d 1 6) (by simp) with h595 | h595
              · linarith only [h595, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h597 | h597
                · rcases m.htr 0 1 3 (by decide) (by decide) with h598 | h598
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h599 | h599
                    · linarith only [h593, h599, hlam]
                    · linarith only [h513, h599, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h561, h598, hlam, p0_1]
                · linarith only [h513, h597, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h604 | h604
              · linarith only [h604, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h606 | h606
                · rcases m.htr 0 1 3 (by decide) (by decide) with h607 | h607
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h608 | h608
                    · linarith only [h593, h608, hlam]
                    · linarith only [h513, h608, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h561, h607, hlam, p0_1]
                · linarith only [h513, h606, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h613 | h613
            · rcases p0_3 (m.d 1 6) (by simp) with h614 | h614
              · linarith only [h614, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h616 | h616
                · rcases m.htr 0 1 3 (by decide) (by decide) with h617 | h617
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h618 | h618
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h619 | h619
                      · linarith only [h613, h619, hlam]
                      · linarith only [h513, h619, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h593, h618, hlam, p0_1]
                  · linarith only [h561, h617, hlam, p0_1]
                · linarith only [h513, h616, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h625 | h625
              · linarith only [h625, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h627 | h627
                · rcases m.htr 0 1 3 (by decide) (by decide) with h628 | h628
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h629 | h629
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h630 | h630
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h631 | h631
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h632 | h632
                          · linarith only [h513, h632, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h634 | h634
                            · linarith only [h561, h632, h634, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h636 | h636
                              · linarith only [h561, h632, h636, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h638 | h638
                                · linarith only [h513, h638, hlam]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
                                  · linarith only [h561, h640, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h642 | h642
                                    · linarith only [h593, h640, h642, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h644 | h644
                                      · linarith only [h561, h644, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h646 | h646
                                        · linarith only [h593, h646, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 4 6 (by decide) (by decide) with h648 | h648
                                          · linarith only [h593, h648, hlam]
                                          · rcases m.htr 1 5 6 (by decide) (by decide) with h650 | h650
                                            · linarith only [h613, h650, hlam]
                                            · rcases m.htr 2 3 4 (by decide) (by decide) with h652 | h652
                                              · rcases m.htr 2 3 5 (by decide) (by decide) with h653 | h653
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h654 | h654
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h655 | h655
                                                    · linarith only [h632, h640, h646, h652, h655, hc12, hc23, hlam, hphi]
                                                    · linarith only [h632, h640, h654, h655, hc12, hc24, hlam, hphi]
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h658 | h658
                                                    · linarith only [h634, h654, h658, hc12, hc34, hlam, hphi, ht23]
                                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h660 | h660
                                                      · linarith only [h632, h640, h646, h650, h653, h660, hc12, hc23, hlam, hphi]
                                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h662 | h662
                                                        · linarith only [h632, h642, h660, h662, hc12, hc45, hlam, hphi, ht23, ht34]
                                                        · linarith only [h632, h640, h652, h654, h662, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                                · linarith only [h632, h640, h652, h653, hc12, hc35, hlam, hphi, ht23]
                                              · rcases m.htr 2 3 5 (by decide) (by decide) with h666 | h666
                                                · linarith only [h632, h642, h652, h666, hc12, hc34, hlam, hphi, ht23]
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h668 | h668
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h669 | h669
                                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h670 | h670
                                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h671 | h671
                                                        · linarith only [h632, h640, h646, h650, h668, h671, hc12, hc24, hlam, hphi]
                                                        · linarith only [h632, h640, h646, h669, h670, h671, hc12, hc34, hlam, hphi, ht23]
                                                      · linarith only [h632, h666, h670, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                                    · linarith only [h632, h652, h668, h669, hc12, hc25, hlam, hphi]
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h676 | h676
                                                    · linarith only [h632, h652, h668, h676, hc12, hc34, hlam, hphi, ht23]
                                                    · linarith only [h632, h652, h676, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h631, hlam, p0_0]
                      · linarith only [h630, hc15, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                    · linarith only [h613, h629, hc14, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h513, h628, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h513, h627, hlam, p0_1]
    · linarith only [h512, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h687 | h687
    · rcases p0_3 (m.d 1 2) (by simp) with h688 | h688
      · rcases p0_3 (m.d 1 3) (by simp) with h689 | h689
        · linarith only [h689, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h691 | h691
          · rcases p0_3 (m.d 1 5) (by simp) with h692 | h692
            · rcases p0_3 (m.d 1 6) (by simp) with h693 | h693
              · rcases m.htr 0 1 2 (by decide) (by decide) with h694 | h694
                · linarith only [h694, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h687, h694, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h697 | h697
                · linarith only [h697, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h687, h697, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h700 | h700
              · rcases m.htr 0 1 2 (by decide) (by decide) with h701 | h701
                · linarith only [h701, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h687, h701, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h704 | h704
                · linarith only [h704, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h687, h704, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h707 | h707
            · rcases p0_3 (m.d 1 6) (by simp) with h708 | h708
              · rcases m.htr 0 1 2 (by decide) (by decide) with h709 | h709
                · linarith only [h709, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h687, h709, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h712 | h712
                · linarith only [h712, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h687, h712, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h715 | h715
              · rcases m.htr 0 1 2 (by decide) (by decide) with h716 | h716
                · linarith only [h716, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h687, h716, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h719 | h719
                · linarith only [h719, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h687, h719, hlam]
      · linarith only [h688, hlam, p0_0]
    · linarith only [h687, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h724 | h724
    · rcases p0_3 (m.d 1 2) (by simp) with h725 | h725
      · rcases p0_3 (m.d 1 3) (by simp) with h726 | h726
        · rcases p0_3 (m.d 1 4) (by simp) with h727 | h727
          · linarith only [h727, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h729 | h729
            · rcases p0_3 (m.d 1 6) (by simp) with h730 | h730
              · rcases m.htr 0 1 2 (by decide) (by decide) with h731 | h731
                · linarith only [h731, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h724, h731, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h734 | h734
                · linarith only [h734, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h724, h734, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h737 | h737
              · rcases m.htr 0 1 2 (by decide) (by decide) with h738 | h738
                · linarith only [h738, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h724, h738, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h741 | h741
                · linarith only [h741, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h724, h741, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h744 | h744
          · linarith only [h744, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h746 | h746
            · rcases p0_3 (m.d 1 6) (by simp) with h747 | h747
              · rcases m.htr 0 1 2 (by decide) (by decide) with h748 | h748
                · linarith only [h726, h748, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h724, h748, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h751 | h751
                · linarith only [h726, h751, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h724, h751, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h754 | h754
              · rcases m.htr 0 1 2 (by decide) (by decide) with h755 | h755
                · linarith only [h726, h755, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h724, h755, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h758 | h758
                · linarith only [h726, h758, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h724, h758, hlam]
      · linarith only [h725, hlam, p0_0]
    · linarith only [h724, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h763 | h763
    · rcases p0_3 (m.d 1 2) (by simp) with h764 | h764
      · rcases p0_3 (m.d 1 3) (by simp) with h765 | h765
        · rcases p0_3 (m.d 1 4) (by simp) with h766 | h766
          · rcases p0_3 (m.d 1 5) (by simp) with h767 | h767
            · linarith only [h767, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h769 | h769
              · rcases m.htr 0 1 2 (by decide) (by decide) with h770 | h770
                · linarith only [h770, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h763, h770, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h773 | h773
                · linarith only [h773, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h763, h773, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h776 | h776
            · linarith only [h776, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h778 | h778
              · rcases m.htr 0 1 2 (by decide) (by decide) with h779 | h779
                · linarith only [h766, h779, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h763, h779, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h782 | h782
                · linarith only [h766, h782, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h763, h782, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h785 | h785
          · rcases p0_3 (m.d 1 5) (by simp) with h786 | h786
            · linarith only [h786, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h788 | h788
              · rcases m.htr 0 1 2 (by decide) (by decide) with h789 | h789
                · linarith only [h765, h789, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h763, h789, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h792 | h792
                · linarith only [h765, h792, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h763, h792, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h795 | h795
            · linarith only [h795, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h797 | h797
              · rcases m.htr 0 1 2 (by decide) (by decide) with h798 | h798
                · linarith only [h765, h798, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h763, h798, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h801 | h801
                · linarith only [h765, h801, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h763, h801, hlam]
      · linarith only [h764, hlam, p0_0]
    · linarith only [h763, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h806 | h806
    · rcases p0_3 (m.d 1 2) (by simp) with h807 | h807
      · rcases p0_3 (m.d 1 3) (by simp) with h808 | h808
        · rcases p0_3 (m.d 1 4) (by simp) with h809 | h809
          · rcases p0_3 (m.d 1 5) (by simp) with h810 | h810
            · rcases p0_3 (m.d 1 6) (by simp) with h811 | h811
              · linarith only [h811, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h813 | h813
                · linarith only [h813, hc01, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                · linarith only [h806, h813, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h816 | h816
              · linarith only [h816, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h818 | h818
                · linarith only [h810, h818, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h806, h818, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h821 | h821
            · rcases p0_3 (m.d 1 6) (by simp) with h822 | h822
              · linarith only [h822, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h824 | h824
                · linarith only [h809, h824, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h806, h824, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h827 | h827
              · linarith only [h827, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h829 | h829
                · linarith only [h809, h829, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h806, h829, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h832 | h832
          · rcases p0_3 (m.d 1 5) (by simp) with h833 | h833
            · rcases p0_3 (m.d 1 6) (by simp) with h834 | h834
              · linarith only [h834, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h836 | h836
                · linarith only [h808, h836, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h806, h836, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h839 | h839
              · linarith only [h839, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h841 | h841
                · linarith only [h808, h841, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h806, h841, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h844 | h844
            · rcases p0_3 (m.d 1 6) (by simp) with h845 | h845
              · linarith only [h845, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h847 | h847
                · linarith only [h808, h847, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h806, h847, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h850 | h850
              · linarith only [h850, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h852 | h852
                · linarith only [h808, h852, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h806, h852, hlam]
      · linarith only [h807, hlam, p0_0]
    · linarith only [h806, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h858 | h858
    · rcases p0_3 (m.d 1 2) (by simp) with h859 | h859
      · linarith only [h859, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h861 | h861
        · rcases p0_3 (m.d 1 4) (by simp) with h862 | h862
          · rcases p0_3 (m.d 1 5) (by simp) with h863 | h863
            · rcases p0_3 (m.d 1 6) (by simp) with h864 | h864
              · rcases m.htr 0 1 2 (by decide) (by decide) with h865 | h865
                · rcases m.htr 0 1 3 (by decide) (by decide) with h866 | h866
                  · linarith only [h866, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h866, hlam]
                · linarith only [h865, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h870 | h870
                · rcases m.htr 0 1 3 (by decide) (by decide) with h871 | h871
                  · linarith only [h871, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h871, hlam]
                · linarith only [h870, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h875 | h875
              · rcases m.htr 0 1 2 (by decide) (by decide) with h876 | h876
                · rcases m.htr 0 1 3 (by decide) (by decide) with h877 | h877
                  · linarith only [h877, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h877, hlam]
                · linarith only [h876, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h881 | h881
                · rcases m.htr 0 1 3 (by decide) (by decide) with h882 | h882
                  · linarith only [h882, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h882, hlam]
                · linarith only [h881, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h886 | h886
            · rcases p0_3 (m.d 1 6) (by simp) with h887 | h887
              · rcases m.htr 0 1 2 (by decide) (by decide) with h888 | h888
                · rcases m.htr 0 1 3 (by decide) (by decide) with h889 | h889
                  · linarith only [h889, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h889, hlam]
                · linarith only [h888, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h893 | h893
                · rcases m.htr 0 1 3 (by decide) (by decide) with h894 | h894
                  · linarith only [h894, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h894, hlam]
                · linarith only [h893, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h898 | h898
              · rcases m.htr 0 1 2 (by decide) (by decide) with h899 | h899
                · rcases m.htr 0 1 3 (by decide) (by decide) with h900 | h900
                  · linarith only [h900, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h900, hlam]
                · linarith only [h899, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h904 | h904
                · rcases m.htr 0 1 3 (by decide) (by decide) with h905 | h905
                  · linarith only [h905, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h905, hlam]
                · linarith only [h904, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h861, hlam, p0_0]
    · linarith only [h858, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h912 | h912
    · rcases p0_3 (m.d 1 2) (by simp) with h913 | h913
      · rcases p0_3 (m.d 1 3) (by simp) with h914 | h914
        · rcases p0_3 (m.d 1 4) (by simp) with h915 | h915
          · linarith only [h915, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h917 | h917
            · rcases p0_3 (m.d 1 6) (by simp) with h918 | h918
              · rcases m.htr 0 1 2 (by decide) (by decide) with h919 | h919
                · linarith only [h913, h919, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h912, h919, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h922 | h922
                · linarith only [h913, h922, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h912, h922, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h925 | h925
              · rcases m.htr 0 1 2 (by decide) (by decide) with h926 | h926
                · linarith only [h913, h926, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h912, h926, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h929 | h929
                · linarith only [h913, h929, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h912, h929, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · linarith only [h914, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h933 | h933
        · rcases p0_3 (m.d 1 4) (by simp) with h934 | h934
          · linarith only [h934, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h936 | h936
            · rcases p0_3 (m.d 1 6) (by simp) with h937 | h937
              · rcases m.htr 0 1 2 (by decide) (by decide) with h938 | h938
                · rcases m.htr 0 1 3 (by decide) (by decide) with h939 | h939
                  · linarith only [h913, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h912, h939, hlam]
                · linarith only [h913, h938, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h943 | h943
                · rcases m.htr 0 1 3 (by decide) (by decide) with h944 | h944
                  · linarith only [h913, h944, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h912, h944, hlam]
                · linarith only [h913, h943, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h948 | h948
              · rcases m.htr 0 1 2 (by decide) (by decide) with h949 | h949
                · rcases m.htr 0 1 3 (by decide) (by decide) with h950 | h950
                  · linarith only [h913, h950, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h912, h950, hlam]
                · linarith only [h913, h949, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h954 | h954
                · rcases m.htr 0 1 3 (by decide) (by decide) with h955 | h955
                  · linarith only [h913, h955, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h912, h955, hlam]
                · linarith only [h913, h954, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h933, hlam, p0_0]
    · linarith only [h912, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h961 | h961
    · rcases p0_3 (m.d 1 2) (by simp) with h962 | h962
      · rcases p0_3 (m.d 1 3) (by simp) with h963 | h963
        · rcases p0_3 (m.d 1 4) (by simp) with h964 | h964
          · rcases p0_3 (m.d 1 5) (by simp) with h965 | h965
            · linarith only [h965, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h967 | h967
              · rcases m.htr 0 1 2 (by decide) (by decide) with h968 | h968
                · linarith only [h962, h968, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h961, h968, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h971 | h971
                · linarith only [h962, h971, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h961, h971, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h974 | h974
            · linarith only [h974, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h976 | h976
              · rcases m.htr 0 1 2 (by decide) (by decide) with h977 | h977
                · linarith only [h962, h964, h977, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h961, h964, h977, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h980 | h980
                · linarith only [h962, h964, h980, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h961, h964, h980, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · linarith only [h963, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h984 | h984
        · rcases p0_3 (m.d 1 4) (by simp) with h985 | h985
          · rcases p0_3 (m.d 1 5) (by simp) with h986 | h986
            · linarith only [h986, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h988 | h988
              · rcases m.htr 0 1 2 (by decide) (by decide) with h989 | h989
                · rcases m.htr 0 1 3 (by decide) (by decide) with h990 | h990
                  · linarith only [h962, h990, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h961, h990, hlam]
                · linarith only [h962, h989, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h994 | h994
                · rcases m.htr 0 1 3 (by decide) (by decide) with h995 | h995
                  · linarith only [h962, h995, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h961, h995, hlam]
                · linarith only [h962, h994, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h999 | h999
            · linarith only [h999, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1001 | h1001
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1002 | h1002
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1003 | h1003
                  · linarith only [h1003, h962, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1003, h961, hlam]
                · linarith only [h1002, h962, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1007 | h1007
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1008 | h1008
                  · linarith only [h1008, h962, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1008, h961, hlam]
                · linarith only [h1007, h962, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h984, hlam, p0_0]
    · linarith only [h961, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1014 | h1014
    · rcases p0_3 (m.d 1 2) (by simp) with h1015 | h1015
      · rcases p0_3 (m.d 1 3) (by simp) with h1016 | h1016
        · rcases p0_3 (m.d 1 4) (by simp) with h1017 | h1017
          · rcases p0_3 (m.d 1 5) (by simp) with h1018 | h1018
            · rcases p0_3 (m.d 1 6) (by simp) with h1019 | h1019
              · linarith only [h1019, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1021 | h1021
                · linarith only [h1015, h1021, hc01, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                · linarith only [h1014, h1021, hc12, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1024 | h1024
              · linarith only [h1024, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1026 | h1026
                · linarith only [h1015, h1018, h1026, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1014, h1018, h1026, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h1029 | h1029
            · rcases p0_3 (m.d 1 6) (by simp) with h1030 | h1030
              · linarith only [h1030, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1032 | h1032
                · linarith only [h1015, h1017, h1032, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1014, h1017, h1032, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1035 | h1035
              · linarith only [h1035, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1037 | h1037
                · linarith only [h1015, h1017, h1037, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1014, h1017, h1037, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · linarith only [h1016, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1041 | h1041
        · rcases p0_3 (m.d 1 4) (by simp) with h1042 | h1042
          · rcases p0_3 (m.d 1 5) (by simp) with h1043 | h1043
            · rcases p0_3 (m.d 1 6) (by simp) with h1044 | h1044
              · linarith only [h1044, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1046 | h1046
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1047 | h1047
                  · linarith only [h1015, h1047, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1014, h1047, hlam]
                · linarith only [h1015, h1046, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1051 | h1051
              · linarith only [h1051, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1053 | h1053
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1054 | h1054
                  · linarith only [h1015, h1054, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1014, h1054, hlam]
                · linarith only [h1015, h1053, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h1058 | h1058
            · rcases p0_3 (m.d 1 6) (by simp) with h1059 | h1059
              · linarith only [h1059, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1061 | h1061
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1062 | h1062
                  · linarith only [h1015, h1062, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1014, h1062, hlam]
                · linarith only [h1015, h1061, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1066 | h1066
              · linarith only [h1066, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1068 | h1068
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1069 | h1069
                  · linarith only [h1015, h1069, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1014, h1069, hlam]
                · linarith only [h1015, h1068, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h1041, hlam, p0_0]
    · linarith only [h1014, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1076 | h1076
    · rcases p0_3 (m.d 1 2) (by simp) with h1077 | h1077
      · linarith only [h1077, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1079 | h1079
        · rcases p0_3 (m.d 1 4) (by simp) with h1080 | h1080
          · rcases p0_3 (m.d 1 5) (by simp) with h1081 | h1081
            · rcases p0_3 (m.d 1 6) (by simp) with h1082 | h1082
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1083 | h1083
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1084 | h1084
                  · linarith only [h1079, h1084, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1076, h1084, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1076, h1083, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1089 | h1089
                  · linarith only [h1079, h1089, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1076, h1089, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1076, h1088, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1093 | h1093
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1094 | h1094
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1095 | h1095
                  · linarith only [h1079, h1095, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1076, h1095, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1076, h1094, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1099 | h1099
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1100 | h1100
                  · linarith only [h1079, h1100, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1076, h1100, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1076, h1099, hlam, p0_1]
          · linarith only [h1080, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1105 | h1105
          · rcases p0_3 (m.d 1 5) (by simp) with h1106 | h1106
            · rcases p0_3 (m.d 1 6) (by simp) with h1107 | h1107
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1108 | h1108
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1109 | h1109
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1110 | h1110
                    · linarith only [h1110, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1076, h1110, hlam]
                  · linarith only [h1079, h1109, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1076, h1108, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1115 | h1115
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1116 | h1116
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1117 | h1117
                    · linarith only [h1117, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1076, h1117, hlam]
                  · linarith only [h1079, h1116, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1076, h1115, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1122 | h1122
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1123 | h1123
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1124 | h1124
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1125 | h1125
                    · linarith only [h1125, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1076, h1125, hlam]
                  · linarith only [h1079, h1124, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1076, h1123, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1130 | h1130
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1131 | h1131
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1132 | h1132
                    · linarith only [h1132, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1076, h1132, hlam]
                  · linarith only [h1079, h1131, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1076, h1130, hlam, p0_1]
          · linarith only [h1105, hlam, p0_0]
    · linarith only [h1076, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1139 | h1139
    · rcases p0_3 (m.d 1 2) (by simp) with h1140 | h1140
      · rcases p0_3 (m.d 1 3) (by simp) with h1141 | h1141
        · linarith only [h1141, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1143 | h1143
          · rcases p0_3 (m.d 1 5) (by simp) with h1144 | h1144
            · rcases p0_3 (m.d 1 6) (by simp) with h1145 | h1145
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1146 | h1146
                · linarith only [h1140, h1146, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1139, h1146, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1149 | h1149
                · linarith only [h1140, h1149, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1139, h1149, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1152 | h1152
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1153 | h1153
                · linarith only [h1140, h1153, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1139, h1153, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1156 | h1156
                · linarith only [h1140, h1156, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1139, h1156, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1143, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1160 | h1160
        · linarith only [h1160, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1162 | h1162
          · rcases p0_3 (m.d 1 5) (by simp) with h1163 | h1163
            · rcases p0_3 (m.d 1 6) (by simp) with h1164 | h1164
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1165 | h1165
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1166 | h1166
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1167 | h1167
                    · linarith only [h1140, h1167, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1139, h1167, hlam]
                  · linarith only [h1166, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1139, h1140, h1165, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1172 | h1172
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1173 | h1173
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1174 | h1174
                    · linarith only [h1140, h1174, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1139, h1174, hlam]
                  · linarith only [h1173, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1139, h1172, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1179 | h1179
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1180 | h1180
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1181 | h1181
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1182 | h1182
                    · linarith only [h1140, h1182, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1139, h1182, hlam]
                  · linarith only [h1181, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1139, h1140, h1180, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1187 | h1187
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1188 | h1188
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1189 | h1189
                    · linarith only [h1140, h1189, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1139, h1189, hlam]
                  · linarith only [h1188, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1139, h1187, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1162, hlam, p0_0]
    · linarith only [h1139, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1197 | h1197
    · rcases p0_3 (m.d 1 2) (by simp) with h1198 | h1198
      · rcases p0_3 (m.d 1 3) (by simp) with h1199 | h1199
        · rcases p0_3 (m.d 1 4) (by simp) with h1200 | h1200
          · rcases p0_3 (m.d 1 5) (by simp) with h1201 | h1201
            · linarith only [h1201, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1203 | h1203
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1204 | h1204
                · linarith only [h1198, h1204, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1197, h1204, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1207 | h1207
                · linarith only [h1198, h1207, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1197, h1207, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · linarith only [h1200, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1211 | h1211
          · rcases p0_3 (m.d 1 5) (by simp) with h1212 | h1212
            · linarith only [h1212, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1214 | h1214
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1215 | h1215
                · linarith only [h1198, h1199, h1215, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1197, h1199, h1215, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1218 | h1218
                · linarith only [h1198, h1199, h1218, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1197, h1199, h1218, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1211, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1222 | h1222
        · rcases p0_3 (m.d 1 4) (by simp) with h1223 | h1223
          · rcases p0_3 (m.d 1 5) (by simp) with h1224 | h1224
            · linarith only [h1224, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1226 | h1226
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1227 | h1227
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1228 | h1228
                  · linarith only [h1198, h1222, h1228, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1197, h1198, h1228, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1197, h1198, h1227, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1232 | h1232
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1233 | h1233
                  · linarith only [h1198, h1222, h1233, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1197, h1198, h1233, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1197, h1198, h1232, hlam, p0_1]
          · linarith only [h1223, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1238 | h1238
          · rcases p0_3 (m.d 1 5) (by simp) with h1239 | h1239
            · linarith only [h1239, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1241 | h1241
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1242 | h1242
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1243 | h1243
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1244 | h1244
                    · linarith only [h1198, h1244, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1197, h1244, hlam]
                  · linarith only [h1222, h1243, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1197, h1198, h1242, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1249 | h1249
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1250 | h1250
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1251 | h1251
                    · linarith only [h1198, h1251, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1197, h1251, hlam]
                  · linarith only [h1222, h1250, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1197, h1222, h1249, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1238, hlam, p0_0]
    · linarith only [h1197, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1258 | h1258
    · rcases p0_3 (m.d 1 2) (by simp) with h1259 | h1259
      · rcases p0_3 (m.d 1 3) (by simp) with h1260 | h1260
        · rcases p0_3 (m.d 1 4) (by simp) with h1261 | h1261
          · rcases p0_3 (m.d 1 5) (by simp) with h1262 | h1262
            · rcases p0_3 (m.d 1 6) (by simp) with h1263 | h1263
              · linarith only [h1263, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1265 | h1265
                · linarith only [h1259, h1265, hc01, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                · linarith only [h1258, h1265, hc12, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1268 | h1268
              · linarith only [h1268, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1270 | h1270
                · linarith only [h1259, h1262, h1270, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1258, h1262, h1270, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · linarith only [h1261, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1274 | h1274
          · rcases p0_3 (m.d 1 5) (by simp) with h1275 | h1275
            · rcases p0_3 (m.d 1 6) (by simp) with h1276 | h1276
              · linarith only [h1276, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1278 | h1278
                · linarith only [h1259, h1260, h1278, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1258, h1260, h1278, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1281 | h1281
              · linarith only [h1281, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1283 | h1283
                · linarith only [h1259, h1260, h1283, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1258, h1260, h1283, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1274, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1287 | h1287
        · rcases p0_3 (m.d 1 4) (by simp) with h1288 | h1288
          · rcases p0_3 (m.d 1 5) (by simp) with h1289 | h1289
            · rcases p0_3 (m.d 1 6) (by simp) with h1290 | h1290
              · linarith only [h1290, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1292 | h1292
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1293 | h1293
                  · linarith only [h1259, h1287, h1293, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1258, h1259, h1293, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1258, h1259, h1292, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1297 | h1297
              · linarith only [h1297, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1299 | h1299
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1300 | h1300
                  · linarith only [h1259, h1287, h1300, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1258, h1259, h1300, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1258, h1259, h1299, hlam, p0_1]
          · linarith only [h1288, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1305 | h1305
          · rcases p0_3 (m.d 1 5) (by simp) with h1306 | h1306
            · rcases p0_3 (m.d 1 6) (by simp) with h1307 | h1307
              · linarith only [h1307, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1309 | h1309
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1310 | h1310
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1311 | h1311
                    · linarith only [h1259, h1311, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1258, h1311, hlam]
                  · linarith only [h1287, h1310, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1258, h1259, h1309, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1316 | h1316
              · linarith only [h1316, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1318 | h1318
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1319 | h1319
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1320 | h1320
                    · linarith only [h1259, h1320, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1258, h1320, hlam]
                  · linarith only [h1287, h1319, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1258, h1287, h1318, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1305, hlam, p0_0]
    · linarith only [h1258, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1328 | h1328
    · rcases p0_3 (m.d 1 2) (by simp) with h1329 | h1329
      · linarith only [h1329, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1331 | h1331
        · rcases p0_3 (m.d 1 4) (by simp) with h1332 | h1332
          · rcases p0_3 (m.d 1 5) (by simp) with h1333 | h1333
            · rcases p0_3 (m.d 1 6) (by simp) with h1334 | h1334
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1335 | h1335
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1336 | h1336
                  · linarith only [h1331, h1336, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1328, h1336, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1328, h1335, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1340 | h1340
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1341 | h1341
                  · linarith only [h1331, h1341, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1328, h1341, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1328, h1340, hlam, p0_1]
            · linarith only [h1333, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1346 | h1346
            · rcases p0_3 (m.d 1 6) (by simp) with h1347 | h1347
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1348 | h1348
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1349 | h1349
                  · linarith only [h1331, h1349, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1328, h1349, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1328, h1348, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1353 | h1353
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1354 | h1354
                  · linarith only [h1331, h1354, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1328, h1354, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1328, h1353, hlam, p0_1]
            · linarith only [h1346, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1359 | h1359
          · rcases p0_3 (m.d 1 5) (by simp) with h1360 | h1360
            · rcases p0_3 (m.d 1 6) (by simp) with h1361 | h1361
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1362 | h1362
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1363 | h1363
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1364 | h1364
                    · linarith only [h1359, h1364, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1328, h1364, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1328, h1331, h1363, hlam, p0_1]
                · linarith only [h1328, h1362, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1369 | h1369
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1370 | h1370
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1371 | h1371
                    · linarith only [h1359, h1371, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1328, h1371, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1328, h1331, h1370, hlam, p0_1]
                · linarith only [h1328, h1369, hlam, p0_1]
            · linarith only [h1360, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1377 | h1377
            · rcases p0_3 (m.d 1 6) (by simp) with h1378 | h1378
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1379 | h1379
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1380 | h1380
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1381 | h1381
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1382 | h1382
                      · linarith only [h1382, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1328, h1382, hlam]
                    · linarith only [h1359, h1381, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1328, h1331, h1380, hlam, p0_1]
                · linarith only [h1328, h1379, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1388 | h1388
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1389 | h1389
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1390 | h1390
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1391 | h1391
                      · linarith only [h1391, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1328, h1391, hlam]
                    · linarith only [h1359, h1390, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1328, h1331, h1389, hlam, p0_1]
                · linarith only [h1328, h1388, hlam, p0_1]
            · linarith only [h1377, hlam, p0_0]
    · linarith only [h1328, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1399 | h1399
    · rcases p0_3 (m.d 1 2) (by simp) with h1400 | h1400
      · rcases p0_3 (m.d 1 3) (by simp) with h1401 | h1401
        · linarith only [h1401, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1403 | h1403
          · rcases p0_3 (m.d 1 5) (by simp) with h1404 | h1404
            · rcases p0_3 (m.d 1 6) (by simp) with h1405 | h1405
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1406 | h1406
                · linarith only [h1400, h1406, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1399, h1406, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1409 | h1409
                · linarith only [h1400, h1409, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1399, h1409, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1404, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1413 | h1413
            · rcases p0_3 (m.d 1 6) (by simp) with h1414 | h1414
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1415 | h1415
                · linarith only [h1400, h1415, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1399, h1415, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1418 | h1418
                · linarith only [h1400, h1418, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1399, h1418, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1413, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1422 | h1422
        · linarith only [h1422, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1424 | h1424
          · rcases p0_3 (m.d 1 5) (by simp) with h1425 | h1425
            · rcases p0_3 (m.d 1 6) (by simp) with h1426 | h1426
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1427 | h1427
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1428 | h1428
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1429 | h1429
                    · linarith only [h1400, h1424, h1429, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1399, h1400, h1429, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1399, h1428, hlam, p0_1]
                · linarith only [h1399, h1400, h1427, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1434 | h1434
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1435 | h1435
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1436 | h1436
                    · linarith only [h1400, h1424, h1436, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1399, h1400, h1436, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1399, h1435, hlam, p0_1]
                · linarith only [h1399, h1400, h1434, hlam, p0_1]
            · linarith only [h1425, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1442 | h1442
            · rcases p0_3 (m.d 1 6) (by simp) with h1443 | h1443
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1444 | h1444
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1445 | h1445
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1446 | h1446
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1447 | h1447
                      · linarith only [h1400, h1447, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1399, h1447, hlam]
                    · linarith only [h1424, h1446, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1399, h1445, hlam, p0_1]
                · linarith only [h1399, h1400, h1444, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1453 | h1453
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1454 | h1454
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1455 | h1455
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1456 | h1456
                      · linarith only [h1400, h1456, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1399, h1456, hlam]
                    · linarith only [h1424, h1455, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1399, h1454, hlam, p0_1]
                · linarith only [h1399, h1453, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1442, hlam, p0_0]
    · linarith only [h1399, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1464 | h1464
    · rcases p0_3 (m.d 1 2) (by simp) with h1465 | h1465
      · rcases p0_3 (m.d 1 3) (by simp) with h1466 | h1466
        · rcases p0_3 (m.d 1 4) (by simp) with h1467 | h1467
          · linarith only [h1467, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1469 | h1469
            · rcases p0_3 (m.d 1 6) (by simp) with h1470 | h1470
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1471 | h1471
                · linarith only [h1465, h1471, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1464, h1471, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1474 | h1474
                · linarith only [h1465, h1474, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1464, h1474, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · linarith only [h1469, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1478 | h1478
          · linarith only [h1478, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1480 | h1480
            · rcases p0_3 (m.d 1 6) (by simp) with h1481 | h1481
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1482 | h1482
                · linarith only [h1465, h1466, h1482, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1464, h1466, h1482, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1485 | h1485
                · linarith only [h1465, h1466, h1485, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1464, h1466, h1485, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1480, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1489 | h1489
        · rcases p0_3 (m.d 1 4) (by simp) with h1490 | h1490
          · linarith only [h1490, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1492 | h1492
            · rcases p0_3 (m.d 1 6) (by simp) with h1493 | h1493
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1494 | h1494
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1495 | h1495
                  · linarith only [h1465, h1489, h1495, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1464, h1465, h1495, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1464, h1465, h1494, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1499 | h1499
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1500 | h1500
                  · linarith only [h1465, h1489, h1500, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1464, h1465, h1500, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1464, h1465, h1499, hlam, p0_1]
            · linarith only [h1492, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1505 | h1505
          · linarith only [h1505, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1507 | h1507
            · rcases p0_3 (m.d 1 6) (by simp) with h1508 | h1508
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1509 | h1509
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1510 | h1510
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1511 | h1511
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1512 | h1512
                      · linarith only [h1465, h1512, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1464, h1512, hlam]
                    · linarith only [h1511, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1464, h1489, h1510, hlam, p0_1]
                · linarith only [h1464, h1465, h1509, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1518 | h1518
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1519 | h1519
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1520 | h1520
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1521 | h1521
                      · linarith only [h1465, h1521, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1464, h1521, hlam]
                    · linarith only [h1520, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1464, h1489, h1519, hlam, p0_1]
                · linarith only [h1464, h1489, h1518, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1507, hlam, p0_0]
    · linarith only [h1464, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1530 | h1530
    · rcases p0_3 (m.d 1 2) (by simp) with h1531 | h1531
      · rcases p0_3 (m.d 1 3) (by simp) with h1532 | h1532
        · rcases p0_3 (m.d 1 4) (by simp) with h1533 | h1533
          · rcases p0_3 (m.d 1 5) (by simp) with h1534 | h1534
            · rcases p0_3 (m.d 1 6) (by simp) with h1535 | h1535
              · linarith only [h1535, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1537 | h1537
                · linarith only [h1531, h1537, hc01, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                · linarith only [h1530, h1537, hc12, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · linarith only [h1534, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1541 | h1541
            · rcases p0_3 (m.d 1 6) (by simp) with h1542 | h1542
              · linarith only [h1542, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1544 | h1544
                · linarith only [h1531, h1533, h1544, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1530, h1533, h1544, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · linarith only [h1541, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1548 | h1548
          · rcases p0_3 (m.d 1 5) (by simp) with h1549 | h1549
            · rcases p0_3 (m.d 1 6) (by simp) with h1550 | h1550
              · linarith only [h1550, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1552 | h1552
                · linarith only [h1531, h1532, h1552, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1530, h1532, h1552, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1549, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1556 | h1556
            · rcases p0_3 (m.d 1 6) (by simp) with h1557 | h1557
              · linarith only [h1557, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1559 | h1559
                · linarith only [h1531, h1532, h1559, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1530, h1532, h1559, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1556, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1563 | h1563
        · rcases p0_3 (m.d 1 4) (by simp) with h1564 | h1564
          · rcases p0_3 (m.d 1 5) (by simp) with h1565 | h1565
            · rcases p0_3 (m.d 1 6) (by simp) with h1566 | h1566
              · linarith only [h1566, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1568 | h1568
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1569 | h1569
                  · linarith only [h1531, h1563, h1569, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1530, h1531, h1569, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1530, h1531, h1568, hlam, p0_1]
            · linarith only [h1565, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1574 | h1574
            · rcases p0_3 (m.d 1 6) (by simp) with h1575 | h1575
              · linarith only [h1575, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1577 | h1577
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1578 | h1578
                  · linarith only [h1531, h1563, h1578, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1530, h1531, h1578, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1530, h1531, h1577, hlam, p0_1]
            · linarith only [h1574, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1583 | h1583
          · rcases p0_3 (m.d 1 5) (by simp) with h1584 | h1584
            · rcases p0_3 (m.d 1 6) (by simp) with h1585 | h1585
              · linarith only [h1585, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1587 | h1587
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1588 | h1588
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1589 | h1589
                    · linarith only [h1531, h1583, h1589, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1530, h1531, h1589, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1530, h1563, h1588, hlam, p0_1]
                · linarith only [h1530, h1531, h1587, hlam, p0_1]
            · linarith only [h1584, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1595 | h1595
            · rcases p0_3 (m.d 1 6) (by simp) with h1596 | h1596
              · linarith only [h1596, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1598 | h1598
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1599 | h1599
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1600 | h1600
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1601 | h1601
                      · linarith only [h1531, h1601, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1530, h1601, hlam]
                    · linarith only [h1583, h1600, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1530, h1563, h1599, hlam, p0_1]
                · linarith only [h1530, h1531, h1598, hlam, p0_1]
            · linarith only [h1595, hlam, p0_0]
    · linarith only [h1530, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1610 | h1610
    · rcases p0_3 (m.d 1 2) (by simp) with h1611 | h1611
      · linarith only [h1611, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1613 | h1613
        · rcases p0_3 (m.d 1 4) (by simp) with h1614 | h1614
          · rcases p0_3 (m.d 1 5) (by simp) with h1615 | h1615
            · rcases p0_3 (m.d 1 6) (by simp) with h1616 | h1616
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1617 | h1617
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1618 | h1618
                  · linarith only [h1613, h1618, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1610, h1618, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1610, h1617, hlam, p0_1]
              · linarith only [h1616, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1623 | h1623
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1624 | h1624
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1625 | h1625
                  · linarith only [h1613, h1625, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1610, h1625, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1610, h1624, hlam, p0_1]
              · linarith only [h1623, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1630 | h1630
            · rcases p0_3 (m.d 1 6) (by simp) with h1631 | h1631
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1632 | h1632
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1633 | h1633
                  · linarith only [h1613, h1633, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1610, h1633, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1610, h1632, hlam, p0_1]
              · linarith only [h1631, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1638 | h1638
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1639 | h1639
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1640 | h1640
                  · linarith only [h1613, h1640, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1610, h1640, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1610, h1639, hlam, p0_1]
              · linarith only [h1638, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1645 | h1645
          · rcases p0_3 (m.d 1 5) (by simp) with h1646 | h1646
            · rcases p0_3 (m.d 1 6) (by simp) with h1647 | h1647
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1648 | h1648
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1649 | h1649
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1650 | h1650
                    · linarith only [h1645, h1650, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1610, h1650, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1610, h1613, h1649, hlam, p0_1]
                · linarith only [h1610, h1648, hlam, p0_1]
              · linarith only [h1647, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1656 | h1656
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1657 | h1657
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1658 | h1658
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1659 | h1659
                    · linarith only [h1645, h1659, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1610, h1659, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1610, h1613, h1658, hlam, p0_1]
                · linarith only [h1610, h1657, hlam, p0_1]
              · linarith only [h1656, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1665 | h1665
            · rcases p0_3 (m.d 1 6) (by simp) with h1666 | h1666
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1667 | h1667
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1668 | h1668
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1669 | h1669
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1670 | h1670
                      · linarith only [h1665, h1670, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1610, h1670, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1610, h1645, h1669, hlam, p0_1]
                  · linarith only [h1610, h1613, h1668, hlam, p0_1]
                · linarith only [h1610, h1667, hlam, p0_1]
              · linarith only [h1666, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1677 | h1677
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1678 | h1678
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1679 | h1679
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1680 | h1680
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1681 | h1681
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1682 | h1682
                        · linarith only [h1682, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1610, h1682, hlam]
                      · linarith only [h1665, h1681, hc01, hc16, hlam, hphi, p0_1]
                    · linarith only [h1610, h1645, h1680, hlam, p0_1]
                  · linarith only [h1610, h1613, h1679, hlam, p0_1]
                · linarith only [h1610, h1678, hlam, p0_1]
              · linarith only [h1677, hlam, p0_0]
    · linarith only [h1610, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1691 | h1691
    · rcases p0_3 (m.d 1 2) (by simp) with h1692 | h1692
      · rcases p0_3 (m.d 1 3) (by simp) with h1693 | h1693
        · linarith only [h1693, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1695 | h1695
          · rcases p0_3 (m.d 1 5) (by simp) with h1696 | h1696
            · rcases p0_3 (m.d 1 6) (by simp) with h1697 | h1697
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1698 | h1698
                · linarith only [h1692, h1698, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1691, h1698, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1697, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1702 | h1702
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1703 | h1703
                · linarith only [h1692, h1703, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1691, h1703, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1702, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1707 | h1707
            · rcases p0_3 (m.d 1 6) (by simp) with h1708 | h1708
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1709 | h1709
                · linarith only [h1692, h1709, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1691, h1709, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1708, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1713 | h1713
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1714 | h1714
                · linarith only [h1692, h1714, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1691, h1714, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1713, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1718 | h1718
        · linarith only [h1718, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1720 | h1720
          · rcases p0_3 (m.d 1 5) (by simp) with h1721 | h1721
            · rcases p0_3 (m.d 1 6) (by simp) with h1722 | h1722
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1723 | h1723
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1724 | h1724
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1725 | h1725
                    · linarith only [h1692, h1720, h1725, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1691, h1692, h1725, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1691, h1724, hlam, p0_1]
                · linarith only [h1691, h1692, h1723, hlam, p0_1]
              · linarith only [h1722, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1731 | h1731
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1732 | h1732
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1733 | h1733
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1734 | h1734
                    · linarith only [h1692, h1720, h1734, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1691, h1692, h1734, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1691, h1733, hlam, p0_1]
                · linarith only [h1691, h1692, h1732, hlam, p0_1]
              · linarith only [h1731, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1740 | h1740
            · rcases p0_3 (m.d 1 6) (by simp) with h1741 | h1741
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1742 | h1742
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1743 | h1743
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1744 | h1744
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1745 | h1745
                      · linarith only [h1692, h1740, h1745, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1691, h1692, h1745, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1691, h1720, h1744, hlam, p0_1]
                  · linarith only [h1691, h1743, hlam, p0_1]
                · linarith only [h1691, h1692, h1742, hlam, p0_1]
              · linarith only [h1741, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1752 | h1752
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1753 | h1753
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1754 | h1754
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1755 | h1755
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1756 | h1756
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1757 | h1757
                        · linarith only [h1692, h1757, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1691, h1757, hlam]
                      · linarith only [h1740, h1756, hc01, hc16, hlam, hphi, p0_1]
                    · linarith only [h1691, h1720, h1755, hlam, p0_1]
                  · linarith only [h1691, h1754, hlam, p0_1]
                · linarith only [h1691, h1692, h1753, hlam, p0_1]
              · linarith only [h1752, hlam, p0_0]
    · linarith only [h1691, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1766 | h1766
    · rcases p0_3 (m.d 1 2) (by simp) with h1767 | h1767
      · rcases p0_3 (m.d 1 3) (by simp) with h1768 | h1768
        · rcases p0_3 (m.d 1 4) (by simp) with h1769 | h1769
          · linarith only [h1769, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1771 | h1771
            · rcases p0_3 (m.d 1 6) (by simp) with h1772 | h1772
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1773 | h1773
                · linarith only [h1767, h1773, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1766, h1773, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h1772, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1777 | h1777
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1778 | h1778
                · linarith only [h1767, h1778, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1766, h1778, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h1777, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1782 | h1782
          · linarith only [h1782, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1784 | h1784
            · rcases p0_3 (m.d 1 6) (by simp) with h1785 | h1785
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1786 | h1786
                · linarith only [h1767, h1768, h1786, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1766, h1768, h1786, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1785, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1790 | h1790
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1791 | h1791
                · linarith only [h1767, h1768, h1791, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1766, h1768, h1791, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1790, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1795 | h1795
        · rcases p0_3 (m.d 1 4) (by simp) with h1796 | h1796
          · linarith only [h1796, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1798 | h1798
            · rcases p0_3 (m.d 1 6) (by simp) with h1799 | h1799
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1800 | h1800
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1801 | h1801
                  · linarith only [h1767, h1795, h1801, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1766, h1767, h1801, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1766, h1767, h1800, hlam, p0_1]
              · linarith only [h1799, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1806 | h1806
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1807 | h1807
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1808 | h1808
                  · linarith only [h1767, h1795, h1808, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1766, h1767, h1808, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1766, h1767, h1807, hlam, p0_1]
              · linarith only [h1806, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1813 | h1813
          · linarith only [h1813, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1815 | h1815
            · rcases p0_3 (m.d 1 6) (by simp) with h1816 | h1816
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1817 | h1817
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1818 | h1818
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1819 | h1819
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1820 | h1820
                      · linarith only [h1767, h1815, h1820, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1766, h1767, h1820, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1766, h1819, hlam, p0_1]
                  · linarith only [h1766, h1795, h1818, hlam, p0_1]
                · linarith only [h1766, h1767, h1817, hlam, p0_1]
              · linarith only [h1816, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1827 | h1827
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1828 | h1828
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1829 | h1829
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1830 | h1830
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1831 | h1831
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1832 | h1832
                        · linarith only [h1767, h1832, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1766, h1832, hlam]
                      · linarith only [h1815, h1831, hc01, hc16, hlam, hphi, p0_1]
                    · linarith only [h1766, h1830, hlam, p0_1]
                  · linarith only [h1766, h1795, h1829, hlam, p0_1]
                · linarith only [h1766, h1767, h1828, hlam, p0_1]
              · linarith only [h1827, hlam, p0_0]
    · linarith only [h1766, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1841 | h1841
    · rcases p0_3 (m.d 1 2) (by simp) with h1842 | h1842
      · rcases p0_3 (m.d 1 3) (by simp) with h1843 | h1843
        · rcases p0_3 (m.d 1 4) (by simp) with h1844 | h1844
          · rcases p0_3 (m.d 1 5) (by simp) with h1845 | h1845
            · linarith only [h1845, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1847 | h1847
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1848 | h1848
                · linarith only [h1842, h1848, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1841, h1848, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h1847, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1852 | h1852
            · linarith only [h1852, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1854 | h1854
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1855 | h1855
                · linarith only [h1842, h1844, h1855, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1841, h1844, h1855, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h1854, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1859 | h1859
          · rcases p0_3 (m.d 1 5) (by simp) with h1860 | h1860
            · linarith only [h1860, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1862 | h1862
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1863 | h1863
                · linarith only [h1842, h1843, h1863, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1841, h1843, h1863, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1862, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1867 | h1867
            · linarith only [h1867, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1869 | h1869
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1870 | h1870
                · linarith only [h1842, h1843, h1870, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1841, h1843, h1870, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1869, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1874 | h1874
        · rcases p0_3 (m.d 1 4) (by simp) with h1875 | h1875
          · rcases p0_3 (m.d 1 5) (by simp) with h1876 | h1876
            · linarith only [h1876, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1878 | h1878
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1879 | h1879
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1880 | h1880
                  · linarith only [h1842, h1874, h1880, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1841, h1842, h1880, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1841, h1842, h1879, hlam, p0_1]
              · linarith only [h1878, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1885 | h1885
            · linarith only [h1885, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1887 | h1887
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1888 | h1888
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1889 | h1889
                  · linarith only [h1842, h1874, h1889, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1841, h1842, h1889, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1841, h1842, h1888, hlam, p0_1]
              · linarith only [h1887, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1894 | h1894
          · rcases p0_3 (m.d 1 5) (by simp) with h1895 | h1895
            · linarith only [h1895, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1897 | h1897
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1898 | h1898
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1899 | h1899
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1900 | h1900
                    · linarith only [h1842, h1894, h1900, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1841, h1842, h1900, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1841, h1874, h1899, hlam, p0_1]
                · linarith only [h1841, h1842, h1898, hlam, p0_1]
              · linarith only [h1897, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1906 | h1906
            · linarith only [h1906, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1908 | h1908
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1909 | h1909
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1910 | h1910
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1911 | h1911
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1912 | h1912
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1913 | h1913
                        · linarith only [h1842, h1913, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1841, h1913, hlam]
                      · linarith only [h1912, hc01, hc16, hlam, hphi, p0_1]
                    · linarith only [h1841, h1894, h1911, hlam, p0_1]
                  · linarith only [h1841, h1874, h1910, hlam, p0_1]
                · linarith only [h1841, h1842, h1909, hlam, p0_1]
              · linarith only [h1908, hlam, p0_0]
    · linarith only [h1841, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

set_option maxHeartbeats 3982000 in
theorem n8l_sAA8_H_R_H_I (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 1 6) (by simp) with h8 | h8
              · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
                · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h5, hlam]
                  · linarith only [h10, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h9, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h14 | h14
                · rcases m.htr 0 1 3 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h5, hlam]
                  · linarith only [h15, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h14, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h19 | h19
              · rcases m.htr 0 1 2 (by decide) (by decide) with h20 | h20
                · rcases m.htr 0 1 3 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, h5, hlam]
                  · linarith only [h21, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h20, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
                  · linarith only [h26, h5, hlam]
                  · linarith only [h26, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h25, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h30 | h30
            · rcases p0_3 (m.d 1 6) (by simp) with h31 | h31
              · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
                · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                  · linarith only [h33, h5, hlam]
                  · linarith only [h33, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h32, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h37 | h37
                · rcases m.htr 0 1 3 (by decide) (by decide) with h38 | h38
                  · linarith only [h38, h5, hlam]
                  · linarith only [h38, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h37, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h42 | h42
              · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
                · rcases m.htr 0 1 3 (by decide) (by decide) with h44 | h44
                  · linarith only [h44, h5, hlam]
                  · linarith only [h44, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h43, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
                · rcases m.htr 0 1 3 (by decide) (by decide) with h49 | h49
                  · linarith only [h49, h5, hlam]
                  · linarith only [h49, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h48, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
          · rcases p0_3 (m.d 1 5) (by simp) with h54 | h54
            · rcases p0_3 (m.d 1 6) (by simp) with h55 | h55
              · rcases m.htr 0 1 2 (by decide) (by decide) with h56 | h56
                · rcases m.htr 0 1 3 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h58 | h58
                    · linarith only [h53, h58, hlam]
                    · linarith only [h58, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h5, h57, hlam, p0_1]
                · linarith only [h56, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 3 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h65 | h65
                    · linarith only [h53, h65, hlam]
                    · linarith only [h65, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h5, h64, hlam, p0_1]
                · linarith only [h63, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h70 | h70
              · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
                · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                    · linarith only [h53, h73, hlam]
                    · linarith only [h73, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h5, h72, hlam, p0_1]
                · linarith only [h71, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h78 | h78
                · rcases m.htr 0 1 3 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h80 | h80
                    · linarith only [h53, h80, hlam]
                    · linarith only [h80, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h5, h79, hlam, p0_1]
                · linarith only [h78, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h85 | h85
            · rcases p0_3 (m.d 1 6) (by simp) with h86 | h86
              · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
                · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
                      · linarith only [h85, h90, hlam]
                      · linarith only [h90, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h53, h89, hlam, p0_1]
                  · linarith only [h5, h88, hlam, p0_1]
                · linarith only [h87, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h96 | h96
                · rcases m.htr 0 1 3 (by decide) (by decide) with h97 | h97
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h99 | h99
                      · linarith only [h85, h99, hlam]
                      · linarith only [h99, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h53, h98, hlam, p0_1]
                  · linarith only [h5, h97, hlam, p0_1]
                · linarith only [h96, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h105 | h105
              · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
                · rcases m.htr 0 1 3 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h110 | h110
                        · linarith only [h105, h110, hlam]
                        · linarith only [h110, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h109, h85, hlam, p0_1]
                    · linarith only [h108, h53, hlam, p0_1]
                  · linarith only [h107, h5, hlam, p0_1]
                · linarith only [h106, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h117 | h117
                · rcases m.htr 0 1 3 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h120 | h120
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h121 | h121
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h122 | h122
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h125 | h125
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                                  · linarith only [h126, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h126, h5, hlam]
                                · linarith only [h125, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                              · linarith only [h123, h124, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                            · linarith only [h123, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h122, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h105, h121, hlam, p0_1]
                      · linarith only [h120, h85, hlam, p0_1]
                    · linarith only [h119, h53, hlam, p0_1]
                  · linarith only [h118, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h117, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h139 | h139
    · rcases p0_3 (m.d 1 2) (by simp) with h140 | h140
      · rcases p0_3 (m.d 1 3) (by simp) with h141 | h141
        · linarith only [h141, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 1 5) (by simp) with h144 | h144
            · rcases p0_3 (m.d 1 6) (by simp) with h145 | h145
              · rcases m.htr 0 1 2 (by decide) (by decide) with h146 | h146
                · linarith only [h140, h146, hlam]
                · linarith only [h146, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h149 | h149
                · linarith only [h140, h149, hlam]
                · linarith only [h149, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h152 | h152
              · rcases m.htr 0 1 2 (by decide) (by decide) with h153 | h153
                · linarith only [h140, h153, hlam]
                · linarith only [h153, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h156 | h156
                · linarith only [h140, h156, hlam]
                · linarith only [h156, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h159 | h159
            · rcases p0_3 (m.d 1 6) (by simp) with h160 | h160
              · rcases m.htr 0 1 2 (by decide) (by decide) with h161 | h161
                · linarith only [h140, h161, hlam]
                · linarith only [h161, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h164 | h164
                · linarith only [h140, h164, hlam]
                · linarith only [h164, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h167 | h167
              · rcases m.htr 0 1 2 (by decide) (by decide) with h168 | h168
                · linarith only [h140, h168, hlam]
                · linarith only [h168, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h171 | h171
                · linarith only [h140, h171, hlam]
                · linarith only [h171, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h174 | h174
        · linarith only [h174, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h176 | h176
          · rcases p0_3 (m.d 1 5) (by simp) with h177 | h177
            · rcases p0_3 (m.d 1 6) (by simp) with h178 | h178
              · rcases m.htr 0 1 2 (by decide) (by decide) with h179 | h179
                · rcases m.htr 0 1 3 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h181 | h181
                    · linarith only [h176, h181, hlam]
                    · linarith only [h140, h181, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h180, hlam, p0_0]
                · linarith only [h140, h179, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h186 | h186
                · rcases m.htr 0 1 3 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h188 | h188
                    · linarith only [h176, h188, hlam]
                    · linarith only [h140, h188, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h187, hlam, p0_0]
                · linarith only [h140, h186, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h193 | h193
              · rcases m.htr 0 1 2 (by decide) (by decide) with h194 | h194
                · rcases m.htr 0 1 3 (by decide) (by decide) with h195 | h195
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h196 | h196
                    · linarith only [h176, h196, hlam]
                    · linarith only [h140, h196, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h195, hlam, p0_0]
                · linarith only [h140, h194, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h201 | h201
                · rcases m.htr 0 1 3 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h203 | h203
                    · linarith only [h176, h203, hlam]
                    · linarith only [h140, h203, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h202, hlam, p0_0]
                · linarith only [h140, h201, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h208 | h208
            · rcases p0_3 (m.d 1 6) (by simp) with h209 | h209
              · rcases m.htr 0 1 2 (by decide) (by decide) with h210 | h210
                · rcases m.htr 0 1 3 (by decide) (by decide) with h211 | h211
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h212 | h212
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h213 | h213
                      · linarith only [h208, h213, hlam]
                      · linarith only [h140, h213, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h176, h212, hlam, p0_1]
                  · linarith only [h211, hlam, p0_0]
                · linarith only [h140, h210, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h219 | h219
                · rcases m.htr 0 1 3 (by decide) (by decide) with h220 | h220
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h208, h222, hlam]
                      · linarith only [h140, h222, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h176, h221, hlam, p0_1]
                  · linarith only [h220, hlam, p0_0]
                · linarith only [h140, h219, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h228 | h228
              · rcases m.htr 0 1 2 (by decide) (by decide) with h229 | h229
                · rcases m.htr 0 1 3 (by decide) (by decide) with h230 | h230
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h231 | h231
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h232 | h232
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h233 | h233
                        · linarith only [h228, h233, hlam]
                        · linarith only [h140, h233, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h208, h232, hlam, p0_1]
                    · linarith only [h176, h231, hlam, p0_1]
                  · linarith only [h230, hlam, p0_0]
                · linarith only [h140, h229, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h240 | h240
                · rcases m.htr 0 1 3 (by decide) (by decide) with h241 | h241
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h242 | h242
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h243 | h243
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h244 | h244
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h245 | h245
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h246 | h246
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h247 | h247
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h248 | h248
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
                                  · linarith only [h140, h249, hlam]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h251 | h251
                                    · linarith only [h249, h251, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h253 | h253
                                      · linarith only [h249, h253, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 6 (by decide) (by decide) with h255 | h255
                                        · linarith only [h249, h255, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                        · rcases m.htr 1 3 4 (by decide) (by decide) with h257 | h257
                                          · linarith only [h257, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h176, h257, hlam]
                                · linarith only [h248, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                              · linarith only [h246, h247, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                            · linarith only [h246, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h245, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h228, h244, hlam, p0_1]
                      · linarith only [h208, h243, hlam, p0_1]
                    · linarith only [h242, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h241, hlam, p0_0]
                · linarith only [h240, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h139, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h270 | h270
    · rcases p0_3 (m.d 1 2) (by simp) with h271 | h271
      · rcases p0_3 (m.d 1 3) (by simp) with h272 | h272
        · rcases p0_3 (m.d 1 4) (by simp) with h273 | h273
          · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h275 | h275
            · rcases p0_3 (m.d 1 6) (by simp) with h276 | h276
              · rcases m.htr 0 1 2 (by decide) (by decide) with h277 | h277
                · linarith only [h271, h277, hlam]
                · linarith only [h277, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h280 | h280
                · linarith only [h271, h280, hlam]
                · linarith only [h280, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h283 | h283
              · rcases m.htr 0 1 2 (by decide) (by decide) with h284 | h284
                · linarith only [h271, h284, hlam]
                · linarith only [h284, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h287 | h287
                · linarith only [h271, h287, hlam]
                · linarith only [h287, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h290 | h290
          · linarith only [h290, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h292 | h292
            · rcases p0_3 (m.d 1 6) (by simp) with h293 | h293
              · rcases m.htr 0 1 2 (by decide) (by decide) with h294 | h294
                · linarith only [h271, h294, hlam]
                · linarith only [h272, h294, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h297 | h297
                · linarith only [h271, h297, hlam]
                · linarith only [h272, h297, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h300 | h300
              · rcases m.htr 0 1 2 (by decide) (by decide) with h301 | h301
                · linarith only [h271, h301, hlam]
                · linarith only [h272, h301, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h304 | h304
                · linarith only [h271, h304, hlam]
                · linarith only [h272, h304, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h307 | h307
        · rcases p0_3 (m.d 1 4) (by simp) with h308 | h308
          · linarith only [h308, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h310 | h310
            · rcases p0_3 (m.d 1 6) (by simp) with h311 | h311
              · rcases m.htr 0 1 2 (by decide) (by decide) with h312 | h312
                · rcases m.htr 0 1 3 (by decide) (by decide) with h313 | h313
                  · linarith only [h307, h313, hlam]
                  · linarith only [h271, h313, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h271, h312, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h317 | h317
                · rcases m.htr 0 1 3 (by decide) (by decide) with h318 | h318
                  · linarith only [h307, h318, hlam]
                  · linarith only [h271, h318, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h271, h317, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h322 | h322
              · rcases m.htr 0 1 2 (by decide) (by decide) with h323 | h323
                · rcases m.htr 0 1 3 (by decide) (by decide) with h324 | h324
                  · linarith only [h307, h324, hlam]
                  · linarith only [h271, h324, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h271, h323, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h328 | h328
                · rcases m.htr 0 1 3 (by decide) (by decide) with h329 | h329
                  · linarith only [h307, h329, hlam]
                  · linarith only [h271, h329, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h271, h328, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h333 | h333
          · linarith only [h333, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h335 | h335
            · rcases p0_3 (m.d 1 6) (by simp) with h336 | h336
              · rcases m.htr 0 1 2 (by decide) (by decide) with h337 | h337
                · rcases m.htr 0 1 3 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h340 | h340
                      · linarith only [h335, h340, hlam]
                      · linarith only [h271, h340, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h339, hlam, p0_0]
                  · linarith only [h307, h338, hlam, p0_1]
                · linarith only [h271, h337, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h346 | h346
                · rcases m.htr 0 1 3 (by decide) (by decide) with h347 | h347
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h348 | h348
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h349 | h349
                      · linarith only [h335, h349, hlam]
                      · linarith only [h271, h349, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h348, hlam, p0_0]
                  · linarith only [h307, h347, hlam, p0_1]
                · linarith only [h271, h346, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h355 | h355
              · rcases m.htr 0 1 2 (by decide) (by decide) with h356 | h356
                · rcases m.htr 0 1 3 (by decide) (by decide) with h357 | h357
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h358 | h358
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h359 | h359
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h360 | h360
                        · linarith only [h355, h360, hlam]
                        · linarith only [h271, h360, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h335, h359, hlam, p0_1]
                    · linarith only [h358, hlam, p0_0]
                  · linarith only [h307, h357, hlam, p0_1]
                · linarith only [h271, h356, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h367 | h367
                · rcases m.htr 0 1 3 (by decide) (by decide) with h368 | h368
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h369 | h369
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h370 | h370
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h371 | h371
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h372 | h372
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h373 | h373
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h374 | h374
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h375 | h375
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
                                  · linarith only [h271, h376, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h378 | h378
                                    · linarith only [h271, h378, hlam]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h380 | h380
                                      · linarith only [h307, h376, h380, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 6 (by decide) (by decide) with h382 | h382
                                        · linarith only [h307, h376, h382, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                        · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                                          · linarith only [h307, h384, hlam]
                                          · rcases m.htr 1 3 5 (by decide) (by decide) with h386 | h386
                                            · linarith only [h384, h386, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                            · rcases m.htr 1 3 6 (by decide) (by decide) with h388 | h388
                                              · linarith only [h384, h388, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                              · rcases m.htr 1 4 5 (by decide) (by decide) with h390 | h390
                                                · linarith only [h390, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                · linarith only [h335, h390, hlam]
                                · linarith only [h375, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                              · linarith only [h373, h374, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                            · linarith only [h373, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h372, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h355, h371, hlam, p0_1]
                      · linarith only [h370, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h369, hlam, p0_0]
                  · linarith only [h368, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h271, h367, hlam, p0_1]
    · linarith only [h270, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h403 | h403
    · rcases p0_3 (m.d 1 2) (by simp) with h404 | h404
      · rcases p0_3 (m.d 1 3) (by simp) with h405 | h405
        · rcases p0_3 (m.d 1 4) (by simp) with h406 | h406
          · rcases p0_3 (m.d 1 5) (by simp) with h407 | h407
            · linarith only [h407, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h409 | h409
              · rcases m.htr 0 1 2 (by decide) (by decide) with h410 | h410
                · linarith only [h404, h410, hlam]
                · linarith only [h410, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h413 | h413
                · linarith only [h404, h413, hlam]
                · linarith only [h413, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h416 | h416
            · linarith only [h416, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h418 | h418
              · rcases m.htr 0 1 2 (by decide) (by decide) with h419 | h419
                · linarith only [h404, h419, hlam]
                · linarith only [h406, h419, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h422 | h422
                · linarith only [h404, h422, hlam]
                · linarith only [h406, h422, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h425 | h425
          · rcases p0_3 (m.d 1 5) (by simp) with h426 | h426
            · linarith only [h426, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h428 | h428
              · rcases m.htr 0 1 2 (by decide) (by decide) with h429 | h429
                · linarith only [h404, h429, hlam]
                · linarith only [h405, h429, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h432 | h432
                · linarith only [h404, h432, hlam]
                · linarith only [h405, h432, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h435 | h435
            · linarith only [h435, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h437 | h437
              · rcases m.htr 0 1 2 (by decide) (by decide) with h438 | h438
                · linarith only [h404, h438, hlam]
                · linarith only [h405, h438, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h441 | h441
                · linarith only [h404, h441, hlam]
                · linarith only [h405, h441, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h444 | h444
        · rcases p0_3 (m.d 1 4) (by simp) with h445 | h445
          · rcases p0_3 (m.d 1 5) (by simp) with h446 | h446
            · linarith only [h446, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h448 | h448
              · rcases m.htr 0 1 2 (by decide) (by decide) with h449 | h449
                · rcases m.htr 0 1 3 (by decide) (by decide) with h450 | h450
                  · linarith only [h444, h450, hlam]
                  · linarith only [h404, h450, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h404, h449, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h454 | h454
                · rcases m.htr 0 1 3 (by decide) (by decide) with h455 | h455
                  · linarith only [h444, h455, hlam]
                  · linarith only [h404, h455, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h404, h454, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h459 | h459
            · linarith only [h459, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h461 | h461
              · rcases m.htr 0 1 2 (by decide) (by decide) with h462 | h462
                · rcases m.htr 0 1 3 (by decide) (by decide) with h463 | h463
                  · linarith only [h444, h463, hlam]
                  · linarith only [h404, h463, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h404, h462, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h467 | h467
                · rcases m.htr 0 1 3 (by decide) (by decide) with h468 | h468
                  · linarith only [h444, h468, hlam]
                  · linarith only [h404, h468, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h404, h467, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h472 | h472
          · rcases p0_3 (m.d 1 5) (by simp) with h473 | h473
            · linarith only [h473, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h475 | h475
              · rcases m.htr 0 1 2 (by decide) (by decide) with h476 | h476
                · rcases m.htr 0 1 3 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h478 | h478
                    · linarith only [h472, h478, hlam]
                    · linarith only [h404, h478, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h444, h477, hlam, p0_1]
                · linarith only [h404, h476, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h483 | h483
                · rcases m.htr 0 1 3 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h485 | h485
                    · linarith only [h472, h485, hlam]
                    · linarith only [h404, h485, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h444, h484, hlam, p0_1]
                · linarith only [h404, h483, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h490 | h490
            · linarith only [h490, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h492 | h492
              · rcases m.htr 0 1 2 (by decide) (by decide) with h493 | h493
                · rcases m.htr 0 1 3 (by decide) (by decide) with h494 | h494
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h495 | h495
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h496 | h496
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h497 | h497
                        · linarith only [h492, h497, hlam]
                        · linarith only [h404, h497, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h496, hlam, p0_0]
                    · linarith only [h472, h495, hlam, p0_1]
                  · linarith only [h444, h494, hlam, p0_1]
                · linarith only [h404, h493, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h504 | h504
                · rcases m.htr 0 1 3 (by decide) (by decide) with h505 | h505
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h506 | h506
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h507 | h507
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h508 | h508
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h509 | h509
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h510 | h510
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h511 | h511
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h512 | h512
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h513 | h513
                                  · linarith only [h404, h513, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h515 | h515
                                    · linarith only [h444, h513, h515, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h517 | h517
                                      · linarith only [h404, h517, hlam]
                                      · rcases m.htr 1 2 6 (by decide) (by decide) with h519 | h519
                                        · linarith only [h444, h513, h519, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                        · rcases m.htr 1 3 4 (by decide) (by decide) with h521 | h521
                                          · linarith only [h444, h521, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                          · rcases m.htr 1 3 5 (by decide) (by decide) with h523 | h523
                                            · linarith only [h444, h523, hlam]
                                            · rcases m.htr 1 3 6 (by decide) (by decide) with h525 | h525
                                              · linarith only [h472, h521, h525, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                              · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
                                                · linarith only [h472, h527, hlam]
                                                · rcases m.htr 1 4 6 (by decide) (by decide) with h529 | h529
                                                  · linarith only [h527, h529, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                  · rcases m.htr 1 5 6 (by decide) (by decide) with h531 | h531
                                                    · linarith only [h531, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                                                    · linarith only [h492, h531, hlam]
                                · linarith only [h512, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                              · linarith only [h510, h511, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                            · linarith only [h510, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h509, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h508, hc15, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h507, hlam, p0_0]
                    · linarith only [h506, hc14, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h404, h505, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h404, h504, hlam, p0_1]
    · linarith only [h403, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h544 | h544
    · rcases p0_3 (m.d 1 2) (by simp) with h545 | h545
      · rcases p0_3 (m.d 1 3) (by simp) with h546 | h546
        · rcases p0_3 (m.d 1 4) (by simp) with h547 | h547
          · rcases p0_3 (m.d 1 5) (by simp) with h548 | h548
            · rcases p0_3 (m.d 1 6) (by simp) with h549 | h549
              · linarith only [h549, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h551 | h551
                · linarith only [h545, h551, hlam]
                · linarith only [h551, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 1 6) (by simp) with h554 | h554
              · linarith only [h554, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h556 | h556
                · linarith only [h545, h556, hlam]
                · linarith only [h548, h556, hc12, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h559 | h559
            · rcases p0_3 (m.d 1 6) (by simp) with h560 | h560
              · linarith only [h560, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h562 | h562
                · linarith only [h545, h562, hlam]
                · linarith only [h547, h562, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h565 | h565
              · linarith only [h565, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h567 | h567
                · linarith only [h545, h567, hlam]
                · linarith only [h547, h567, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h570 | h570
          · rcases p0_3 (m.d 1 5) (by simp) with h571 | h571
            · rcases p0_3 (m.d 1 6) (by simp) with h572 | h572
              · linarith only [h572, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h574 | h574
                · linarith only [h545, h574, hlam]
                · linarith only [h546, h574, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h577 | h577
              · linarith only [h577, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h579 | h579
                · linarith only [h545, h579, hlam]
                · linarith only [h546, h579, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h582 | h582
            · rcases p0_3 (m.d 1 6) (by simp) with h583 | h583
              · linarith only [h583, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h585 | h585
                · linarith only [h545, h585, hlam]
                · linarith only [h546, h585, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h588 | h588
              · linarith only [h588, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h590 | h590
                · linarith only [h545, h590, hlam]
                · linarith only [h546, h590, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 1 3) (by simp) with h593 | h593
        · rcases p0_3 (m.d 1 4) (by simp) with h594 | h594
          · rcases p0_3 (m.d 1 5) (by simp) with h595 | h595
            · rcases p0_3 (m.d 1 6) (by simp) with h596 | h596
              · linarith only [h596, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h598 | h598
                · rcases m.htr 0 1 3 (by decide) (by decide) with h599 | h599
                  · linarith only [h593, h599, hlam]
                  · linarith only [h545, h599, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h545, h598, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h603 | h603
              · linarith only [h603, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h605 | h605
                · rcases m.htr 0 1 3 (by decide) (by decide) with h606 | h606
                  · linarith only [h593, h606, hlam]
                  · linarith only [h545, h606, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h545, h605, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h610 | h610
            · rcases p0_3 (m.d 1 6) (by simp) with h611 | h611
              · linarith only [h611, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h613 | h613
                · rcases m.htr 0 1 3 (by decide) (by decide) with h614 | h614
                  · linarith only [h593, h614, hlam]
                  · linarith only [h545, h614, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h545, h613, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h618 | h618
              · linarith only [h618, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h620 | h620
                · rcases m.htr 0 1 3 (by decide) (by decide) with h621 | h621
                  · linarith only [h593, h621, hlam]
                  · linarith only [h545, h621, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h545, h620, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h625 | h625
          · rcases p0_3 (m.d 1 5) (by simp) with h626 | h626
            · rcases p0_3 (m.d 1 6) (by simp) with h627 | h627
              · linarith only [h627, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h629 | h629
                · rcases m.htr 0 1 3 (by decide) (by decide) with h630 | h630
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h631 | h631
                    · linarith only [h625, h631, hlam]
                    · linarith only [h545, h631, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h593, h630, hlam, p0_1]
                · linarith only [h545, h629, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h636 | h636
              · linarith only [h636, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h638 | h638
                · rcases m.htr 0 1 3 (by decide) (by decide) with h639 | h639
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h640 | h640
                    · linarith only [h625, h640, hlam]
                    · linarith only [h545, h640, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h593, h639, hlam, p0_1]
                · linarith only [h545, h638, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h645 | h645
            · rcases p0_3 (m.d 1 6) (by simp) with h646 | h646
              · linarith only [h646, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h648 | h648
                · rcases m.htr 0 1 3 (by decide) (by decide) with h649 | h649
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h650 | h650
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h651 | h651
                      · linarith only [h645, h651, hlam]
                      · linarith only [h545, h651, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h625, h650, hlam, p0_1]
                  · linarith only [h593, h649, hlam, p0_1]
                · linarith only [h545, h648, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h657 | h657
              · linarith only [h657, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h659 | h659
                · rcases m.htr 0 1 3 (by decide) (by decide) with h660 | h660
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h661 | h661
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h662 | h662
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h663 | h663
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h664 | h664
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h665 | h665
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h666 | h666
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h667 | h667
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h668 | h668
                                  · linarith only [h545, h668, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h670 | h670
                                    · linarith only [h593, h668, h670, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h672 | h672
                                      · linarith only [h593, h668, h672, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 6 (by decide) (by decide) with h674 | h674
                                        · linarith only [h545, h674, hlam]
                                        · rcases m.htr 1 3 4 (by decide) (by decide) with h676 | h676
                                          · linarith only [h593, h676, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                          · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                                            · linarith only [h625, h676, h678, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                            · rcases m.htr 1 3 6 (by decide) (by decide) with h680 | h680
                                              · linarith only [h593, h680, hlam]
                                              · rcases m.htr 1 4 5 (by decide) (by decide) with h682 | h682
                                                · linarith only [h625, h682, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                · rcases m.htr 1 4 6 (by decide) (by decide) with h684 | h684
                                                  · linarith only [h625, h684, hlam]
                                                  · rcases m.htr 1 5 6 (by decide) (by decide) with h686 | h686
                                                    · linarith only [h645, h686, hlam]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h688 | h688
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h689 | h689
                                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h690 | h690
                                                          · rcases m.htr 2 4 6 (by decide) (by decide) with h691 | h691
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h692 | h692
                                                              · rcases m.htr 3 4 6 (by decide) (by decide) with h693 | h693
                                                                · linarith only [h659, h664, h668, h676, h684, h688, h693, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                                · linarith only [h659, h664, h668, h676, h688, h691, h693, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                              · rcases m.htr 3 4 6 (by decide) (by decide) with h696 | h696
                                                                · linarith only [h659, h664, h668, h676, h684, h688, h696, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                                · linarith only [h659, h664, h668, h676, h688, h691, h696, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                            · linarith only [h659, h664, h665, h667, h668, h676, h682, h690, h691, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                          · rcases m.htr 2 4 6 (by decide) (by decide) with h700 | h700
                                                            · linarith only [h668, h676, h684, h690, h700, hc12, hc45, hlam, hphi, ht23, ht34]
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h702 | h702
                                                              · rcases m.htr 3 4 6 (by decide) (by decide) with h703 | h703
                                                                · linarith only [h659, h664, h665, h670, h700, h703, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h705 | h705
                                                                  · linarith only [h659, h664, h668, h676, h682, h686, h689, h705, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                                  · linarith only [h668, h678, h702, h705, hc12, hc25, hlam, hphi]
                                                              · rcases m.htr 3 4 6 (by decide) (by decide) with h708 | h708
                                                                · linarith only [h688, h700, h708, hlam]
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h710 | h710
                                                                  · linarith only [h659, h664, h666, h672, h702, h710, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                                  · rcases m.htr 4 5 6 (by decide) (by decide) with h712 | h712
                                                                    · linarith only [h668, h676, h688, h690, h702, h712, hc12, hc45, hlam, hphi, ht23, ht34]
                                                                    · linarith only [h668, h676, h688, h690, h712, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                                        · linarith only [h659, h664, h666, h668, h676, h688, h689, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h716 | h716
                                                        · linarith only [h668, h678, h688, h716, hc12, hc34, hlam, hphi, ht23]
                                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h718 | h718
                                                          · rcases m.htr 2 4 6 (by decide) (by decide) with h719 | h719
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h720 | h720
                                                              · rcases m.htr 3 4 6 (by decide) (by decide) with h721 | h721
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h722 | h722
                                                                  · rcases m.htr 4 5 6 (by decide) (by decide) with h723 | h723
                                                                    · linarith only [h668, h676, h682, h686, h718, h723, hc12, hc24, hlam, hphi]
                                                                    · linarith only [h668, h676, h682, h720, h723, hc12, hc25, hlam, hphi]
                                                                  · linarith only [h659, h664, h665, h668, h678, h688, h718, h720, h722, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                                · linarith only [h688, h719, h721, hlam]
                                                              · rcases m.htr 3 4 6 (by decide) (by decide) with h728 | h728
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h729 | h729
                                                                  · linarith only [h659, h664, h666, h672, h720, h729, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                                  · linarith only [h668, h716, h729, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                                                · linarith only [h688, h719, h728, hlam]
                                                            · linarith only [h659, h664, h665, h667, h668, h676, h682, h718, h719, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                          · rcases m.htr 2 4 6 (by decide) (by decide) with h734 | h734
                                                            · linarith only [h668, h676, h684, h718, h734, hc12, hc45, hlam, hphi, ht23, ht34]
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h736 | h736
                                                              · rcases m.htr 3 4 6 (by decide) (by decide) with h737 | h737
                                                                · linarith only [h659, h664, h665, h670, h734, h737, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                                · linarith only [h668, h688, h737, hc12, hc46, hlam, hphi, ht23, ht34]
                                                              · rcases m.htr 3 4 6 (by decide) (by decide) with h740 | h740
                                                                · linarith only [h659, h664, h665, h668, h688, h734, h740, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                                                · linarith only [h668, h688, h740, hc12, hc46, hlam, hphi, ht23, ht34]
                                · linarith only [h667, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                              · linarith only [h666, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                            · linarith only [h665, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h664, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h663, hlam, p0_0]
                      · linarith only [h625, h662, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h545, h661, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h593, h660, hlam, p0_1]
                · linarith only [h545, h659, hlam, p0_1]
    · linarith only [h544, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h755 | h755
    · rcases p0_3 (m.d 1 2) (by simp) with h756 | h756
      · rcases p0_3 (m.d 1 3) (by simp) with h757 | h757
        · linarith only [h757, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h759 | h759
          · rcases p0_3 (m.d 1 5) (by simp) with h760 | h760
            · rcases p0_3 (m.d 1 6) (by simp) with h761 | h761
              · rcases m.htr 0 1 2 (by decide) (by decide) with h762 | h762
                · linarith only [h762, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h755, h762, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h765 | h765
                · linarith only [h765, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h755, h765, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h768 | h768
              · rcases m.htr 0 1 2 (by decide) (by decide) with h769 | h769
                · linarith only [h769, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h755, h769, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h772 | h772
                · linarith only [h772, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h755, h772, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h775 | h775
            · rcases p0_3 (m.d 1 6) (by simp) with h776 | h776
              · rcases m.htr 0 1 2 (by decide) (by decide) with h777 | h777
                · linarith only [h777, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h755, h777, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h780 | h780
                · linarith only [h780, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h755, h780, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h783 | h783
              · rcases m.htr 0 1 2 (by decide) (by decide) with h784 | h784
                · linarith only [h784, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h755, h784, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h787 | h787
                · linarith only [h787, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h755, h787, hlam]
      · linarith only [h756, hlam, p0_0]
    · linarith only [h755, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h792 | h792
    · rcases p0_3 (m.d 1 2) (by simp) with h793 | h793
      · rcases p0_3 (m.d 1 3) (by simp) with h794 | h794
        · rcases p0_3 (m.d 1 4) (by simp) with h795 | h795
          · linarith only [h795, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h797 | h797
            · rcases p0_3 (m.d 1 6) (by simp) with h798 | h798
              · rcases m.htr 0 1 2 (by decide) (by decide) with h799 | h799
                · linarith only [h799, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h792, h799, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h802 | h802
                · linarith only [h802, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h792, h802, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h805 | h805
              · rcases m.htr 0 1 2 (by decide) (by decide) with h806 | h806
                · linarith only [h806, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h792, h806, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h809 | h809
                · linarith only [h809, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h792, h809, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h812 | h812
          · linarith only [h812, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h814 | h814
            · rcases p0_3 (m.d 1 6) (by simp) with h815 | h815
              · rcases m.htr 0 1 2 (by decide) (by decide) with h816 | h816
                · linarith only [h794, h816, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h792, h816, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h819 | h819
                · linarith only [h794, h819, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h792, h819, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h822 | h822
              · rcases m.htr 0 1 2 (by decide) (by decide) with h823 | h823
                · linarith only [h794, h823, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h792, h823, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h826 | h826
                · linarith only [h794, h826, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h792, h826, hlam]
      · linarith only [h793, hlam, p0_0]
    · linarith only [h792, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h831 | h831
    · rcases p0_3 (m.d 1 2) (by simp) with h832 | h832
      · rcases p0_3 (m.d 1 3) (by simp) with h833 | h833
        · rcases p0_3 (m.d 1 4) (by simp) with h834 | h834
          · rcases p0_3 (m.d 1 5) (by simp) with h835 | h835
            · linarith only [h835, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h837 | h837
              · rcases m.htr 0 1 2 (by decide) (by decide) with h838 | h838
                · linarith only [h838, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h831, h838, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h841 | h841
                · linarith only [h841, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h831, h841, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h844 | h844
            · linarith only [h844, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h846 | h846
              · rcases m.htr 0 1 2 (by decide) (by decide) with h847 | h847
                · linarith only [h834, h847, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h831, h847, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h850 | h850
                · linarith only [h834, h850, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h831, h850, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h853 | h853
          · rcases p0_3 (m.d 1 5) (by simp) with h854 | h854
            · linarith only [h854, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h856 | h856
              · rcases m.htr 0 1 2 (by decide) (by decide) with h857 | h857
                · linarith only [h833, h857, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h831, h857, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h860 | h860
                · linarith only [h833, h860, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h831, h860, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h863 | h863
            · linarith only [h863, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h865 | h865
              · rcases m.htr 0 1 2 (by decide) (by decide) with h866 | h866
                · linarith only [h833, h866, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h831, h866, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h869 | h869
                · linarith only [h833, h869, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h831, h869, hlam]
      · linarith only [h832, hlam, p0_0]
    · linarith only [h831, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h874 | h874
    · rcases p0_3 (m.d 1 2) (by simp) with h875 | h875
      · rcases p0_3 (m.d 1 3) (by simp) with h876 | h876
        · rcases p0_3 (m.d 1 4) (by simp) with h877 | h877
          · rcases p0_3 (m.d 1 5) (by simp) with h878 | h878
            · rcases p0_3 (m.d 1 6) (by simp) with h879 | h879
              · linarith only [h879, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h881 | h881
                · linarith only [h881, hc01, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                · linarith only [h874, h881, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h884 | h884
              · linarith only [h884, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h886 | h886
                · linarith only [h878, h886, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h874, h886, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h889 | h889
            · rcases p0_3 (m.d 1 6) (by simp) with h890 | h890
              · linarith only [h890, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h892 | h892
                · linarith only [h877, h892, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h892, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h895 | h895
              · linarith only [h895, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h897 | h897
                · linarith only [h877, h897, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h897, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h900 | h900
          · rcases p0_3 (m.d 1 5) (by simp) with h901 | h901
            · rcases p0_3 (m.d 1 6) (by simp) with h902 | h902
              · linarith only [h902, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h904 | h904
                · linarith only [h876, h904, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h904, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h907 | h907
              · linarith only [h907, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h909 | h909
                · linarith only [h876, h909, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h909, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h912 | h912
            · rcases p0_3 (m.d 1 6) (by simp) with h913 | h913
              · linarith only [h913, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h915 | h915
                · linarith only [h876, h915, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h915, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h918 | h918
              · linarith only [h918, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h920 | h920
                · linarith only [h876, h920, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h920, hlam]
      · linarith only [h875, hlam, p0_0]
    · linarith only [h874, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h926 | h926
    · rcases p0_3 (m.d 1 2) (by simp) with h927 | h927
      · linarith only [h927, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h929 | h929
        · rcases p0_3 (m.d 1 4) (by simp) with h930 | h930
          · rcases p0_3 (m.d 1 5) (by simp) with h931 | h931
            · rcases p0_3 (m.d 1 6) (by simp) with h932 | h932
              · rcases m.htr 0 1 2 (by decide) (by decide) with h933 | h933
                · rcases m.htr 0 1 3 (by decide) (by decide) with h934 | h934
                  · linarith only [h934, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h926, h934, hlam]
                · linarith only [h933, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h938 | h938
                · rcases m.htr 0 1 3 (by decide) (by decide) with h939 | h939
                  · linarith only [h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h926, h939, hlam]
                · linarith only [h938, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h943 | h943
              · rcases m.htr 0 1 2 (by decide) (by decide) with h944 | h944
                · rcases m.htr 0 1 3 (by decide) (by decide) with h945 | h945
                  · linarith only [h945, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h926, h945, hlam]
                · linarith only [h944, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h949 | h949
                · rcases m.htr 0 1 3 (by decide) (by decide) with h950 | h950
                  · linarith only [h950, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h926, h950, hlam]
                · linarith only [h949, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h954 | h954
            · rcases p0_3 (m.d 1 6) (by simp) with h955 | h955
              · rcases m.htr 0 1 2 (by decide) (by decide) with h956 | h956
                · rcases m.htr 0 1 3 (by decide) (by decide) with h957 | h957
                  · linarith only [h957, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h926, h957, hlam]
                · linarith only [h956, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h961 | h961
                · rcases m.htr 0 1 3 (by decide) (by decide) with h962 | h962
                  · linarith only [h962, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h926, h962, hlam]
                · linarith only [h961, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h966 | h966
              · rcases m.htr 0 1 2 (by decide) (by decide) with h967 | h967
                · rcases m.htr 0 1 3 (by decide) (by decide) with h968 | h968
                  · linarith only [h968, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h926, h968, hlam]
                · linarith only [h967, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h972 | h972
                · rcases m.htr 0 1 3 (by decide) (by decide) with h973 | h973
                  · linarith only [h973, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h926, h973, hlam]
                · linarith only [h972, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h929, hlam, p0_0]
    · linarith only [h926, hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h980 | h980
    · rcases p0_3 (m.d 1 2) (by simp) with h981 | h981
      · rcases p0_3 (m.d 1 3) (by simp) with h982 | h982
        · rcases p0_3 (m.d 1 4) (by simp) with h983 | h983
          · linarith only [h983, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h985 | h985
            · rcases p0_3 (m.d 1 6) (by simp) with h986 | h986
              · rcases m.htr 0 1 2 (by decide) (by decide) with h987 | h987
                · linarith only [h981, h987, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h987, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h990 | h990
                · linarith only [h981, h990, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h990, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 1 6) (by simp) with h993 | h993
              · rcases m.htr 0 1 2 (by decide) (by decide) with h994 | h994
                · linarith only [h981, h994, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h994, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h997 | h997
                · linarith only [h981, h997, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h997, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h982, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1001 | h1001
        · rcases p0_3 (m.d 1 4) (by simp) with h1002 | h1002
          · linarith only [h1002, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1004 | h1004
            · rcases p0_3 (m.d 1 6) (by simp) with h1005 | h1005
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1006 | h1006
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1007 | h1007
                  · linarith only [h1007, h981, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1007, h980, hlam]
                · linarith only [h1006, h981, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1011 | h1011
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1012 | h1012
                  · linarith only [h1012, h981, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1012, h980, hlam]
                · linarith only [h1011, h981, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1016 | h1016
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1017 | h1017
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1018 | h1018
                  · linarith only [h1018, h981, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1018, h980, hlam]
                · linarith only [h1017, h981, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1022 | h1022
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1023 | h1023
                  · linarith only [h1023, h981, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1023, h980, hlam]
                · linarith only [h1022, h981, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h1001, hlam, p0_0]
    · linarith only [h980, hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1029 | h1029
    · rcases p0_3 (m.d 1 2) (by simp) with h1030 | h1030
      · rcases p0_3 (m.d 1 3) (by simp) with h1031 | h1031
        · rcases p0_3 (m.d 1 4) (by simp) with h1032 | h1032
          · rcases p0_3 (m.d 1 5) (by simp) with h1033 | h1033
            · linarith only [h1033, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1035 | h1035
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1036 | h1036
                · linarith only [h1030, h1036, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1036, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1039 | h1039
                · linarith only [h1030, h1039, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1039, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1042 | h1042
            · linarith only [h1042, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1044 | h1044
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1045 | h1045
                · linarith only [h1030, h1032, h1045, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1045, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1048 | h1048
                · linarith only [h1030, h1032, h1048, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1048, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h1031, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1052 | h1052
        · rcases p0_3 (m.d 1 4) (by simp) with h1053 | h1053
          · rcases p0_3 (m.d 1 5) (by simp) with h1054 | h1054
            · linarith only [h1054, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1056 | h1056
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1057 | h1057
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1058 | h1058
                  · linarith only [h1030, h1058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1029, h1058, hlam]
                · linarith only [h1030, h1057, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1062 | h1062
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1063 | h1063
                  · linarith only [h1030, h1063, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1029, h1063, hlam]
                · linarith only [h1030, h1062, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h1067 | h1067
            · linarith only [h1067, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1069 | h1069
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1070 | h1070
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1071 | h1071
                  · linarith only [h1030, h1071, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1029, h1071, hlam]
                · linarith only [h1030, h1070, hc01, hc13, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1075 | h1075
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1076 | h1076
                  · linarith only [h1030, h1076, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1029, h1076, hlam]
                · linarith only [h1030, h1075, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h1052, hlam, p0_0]
    · linarith only [h1029, hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1082 | h1082
    · rcases p0_3 (m.d 1 2) (by simp) with h1083 | h1083
      · rcases p0_3 (m.d 1 3) (by simp) with h1084 | h1084
        · rcases p0_3 (m.d 1 4) (by simp) with h1085 | h1085
          · rcases p0_3 (m.d 1 5) (by simp) with h1086 | h1086
            · rcases p0_3 (m.d 1 6) (by simp) with h1087 | h1087
              · linarith only [h1087, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1089 | h1089
                · linarith only [h1083, h1089, hc01, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                · linarith only [h1089, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1092 | h1092
              · linarith only [h1092, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1094 | h1094
                · linarith only [h1083, h1086, h1094, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1094, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1097 | h1097
            · rcases p0_3 (m.d 1 6) (by simp) with h1098 | h1098
              · linarith only [h1098, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1100 | h1100
                · linarith only [h1083, h1085, h1100, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1100, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1103 | h1103
              · linarith only [h1103, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1105 | h1105
                · linarith only [h1083, h1085, h1105, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1105, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h1084, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1109 | h1109
        · rcases p0_3 (m.d 1 4) (by simp) with h1110 | h1110
          · rcases p0_3 (m.d 1 5) (by simp) with h1111 | h1111
            · rcases p0_3 (m.d 1 6) (by simp) with h1112 | h1112
              · linarith only [h1112, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1114 | h1114
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1115 | h1115
                  · linarith only [h1083, h1115, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1082, h1115, hlam]
                · linarith only [h1083, h1114, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1119 | h1119
              · linarith only [h1119, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1121 | h1121
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1122 | h1122
                  · linarith only [h1083, h1122, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1082, h1122, hlam]
                · linarith only [h1083, h1121, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h1126 | h1126
            · rcases p0_3 (m.d 1 6) (by simp) with h1127 | h1127
              · linarith only [h1127, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1129 | h1129
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1130 | h1130
                  · linarith only [h1083, h1130, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1082, h1130, hlam]
                · linarith only [h1083, h1129, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1134 | h1134
              · linarith only [h1134, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1136 | h1136
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1137 | h1137
                  · linarith only [h1083, h1137, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1082, h1137, hlam]
                · linarith only [h1083, h1136, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h1109, hlam, p0_0]
    · linarith only [h1082, hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1144 | h1144
    · rcases p0_3 (m.d 1 2) (by simp) with h1145 | h1145
      · linarith only [h1145, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1147 | h1147
        · rcases p0_3 (m.d 1 4) (by simp) with h1148 | h1148
          · rcases p0_3 (m.d 1 5) (by simp) with h1149 | h1149
            · rcases p0_3 (m.d 1 6) (by simp) with h1150 | h1150
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1151 | h1151
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1152 | h1152
                  · linarith only [h1147, h1152, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1152, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1144, h1151, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1156 | h1156
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1157 | h1157
                  · linarith only [h1147, h1157, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1157, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1144, h1156, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1161 | h1161
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1162 | h1162
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1163 | h1163
                  · linarith only [h1147, h1163, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1163, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1144, h1162, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1167 | h1167
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1168 | h1168
                  · linarith only [h1147, h1168, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1168, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1144, h1167, hlam, p0_1]
          · linarith only [h1148, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1173 | h1173
          · rcases p0_3 (m.d 1 5) (by simp) with h1174 | h1174
            · rcases p0_3 (m.d 1 6) (by simp) with h1175 | h1175
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1176 | h1176
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1177 | h1177
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1178 | h1178
                    · linarith only [h1178, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1144, h1178, hlam]
                  · linarith only [h1147, h1177, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1144, h1176, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1183 | h1183
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1184 | h1184
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1185 | h1185
                    · linarith only [h1185, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1144, h1185, hlam]
                  · linarith only [h1147, h1184, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1144, h1183, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1190 | h1190
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1191 | h1191
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1192 | h1192
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1193 | h1193
                    · linarith only [h1193, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1144, h1193, hlam]
                  · linarith only [h1147, h1192, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1144, h1191, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1198 | h1198
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1199 | h1199
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1200 | h1200
                    · linarith only [h1200, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1144, h1200, hlam]
                  · linarith only [h1147, h1199, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1144, h1198, hlam, p0_1]
          · linarith only [h1173, hlam, p0_0]
    · linarith only [h1144, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1207 | h1207
    · rcases p0_3 (m.d 1 2) (by simp) with h1208 | h1208
      · rcases p0_3 (m.d 1 3) (by simp) with h1209 | h1209
        · linarith only [h1209, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1211 | h1211
          · rcases p0_3 (m.d 1 5) (by simp) with h1212 | h1212
            · rcases p0_3 (m.d 1 6) (by simp) with h1213 | h1213
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1214 | h1214
                · linarith only [h1208, h1214, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1214, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1217 | h1217
                · linarith only [h1208, h1217, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1217, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1220 | h1220
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1221 | h1221
                · linarith only [h1208, h1221, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1221, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1224 | h1224
                · linarith only [h1208, h1224, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1224, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h1211, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1228 | h1228
        · linarith only [h1228, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1230 | h1230
          · rcases p0_3 (m.d 1 5) (by simp) with h1231 | h1231
            · rcases p0_3 (m.d 1 6) (by simp) with h1232 | h1232
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1233 | h1233
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1234 | h1234
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1235 | h1235
                    · linarith only [h1208, h1235, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1207, h1235, hlam]
                  · linarith only [h1234, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1207, h1208, h1233, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1240 | h1240
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1241 | h1241
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1242 | h1242
                    · linarith only [h1208, h1242, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1207, h1242, hlam]
                  · linarith only [h1241, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1207, h1240, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1247 | h1247
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1248 | h1248
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1249 | h1249
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1250 | h1250
                    · linarith only [h1208, h1250, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1207, h1250, hlam]
                  · linarith only [h1249, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1207, h1208, h1248, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1255 | h1255
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1256 | h1256
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1257 | h1257
                    · linarith only [h1208, h1257, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1207, h1257, hlam]
                  · linarith only [h1256, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1207, h1255, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1230, hlam, p0_0]
    · linarith only [h1207, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1265 | h1265
    · rcases p0_3 (m.d 1 2) (by simp) with h1266 | h1266
      · rcases p0_3 (m.d 1 3) (by simp) with h1267 | h1267
        · rcases p0_3 (m.d 1 4) (by simp) with h1268 | h1268
          · rcases p0_3 (m.d 1 5) (by simp) with h1269 | h1269
            · linarith only [h1269, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1271 | h1271
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1272 | h1272
                · linarith only [h1266, h1272, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1272, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1275 | h1275
                · linarith only [h1266, h1275, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1275, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h1268, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1279 | h1279
          · rcases p0_3 (m.d 1 5) (by simp) with h1280 | h1280
            · linarith only [h1280, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1282 | h1282
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1283 | h1283
                · linarith only [h1266, h1267, h1283, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1283, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1286 | h1286
                · linarith only [h1266, h1267, h1286, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1286, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h1279, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1290 | h1290
        · rcases p0_3 (m.d 1 4) (by simp) with h1291 | h1291
          · rcases p0_3 (m.d 1 5) (by simp) with h1292 | h1292
            · linarith only [h1292, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1294 | h1294
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1295 | h1295
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1296 | h1296
                  · linarith only [h1266, h1290, h1296, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1296, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1265, h1266, h1295, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1300 | h1300
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1301 | h1301
                  · linarith only [h1266, h1290, h1301, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1301, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1265, h1266, h1300, hlam, p0_1]
          · linarith only [h1291, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1306 | h1306
          · rcases p0_3 (m.d 1 5) (by simp) with h1307 | h1307
            · linarith only [h1307, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1309 | h1309
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1310 | h1310
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1311 | h1311
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1312 | h1312
                    · linarith only [h1266, h1312, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1265, h1312, hlam]
                  · linarith only [h1290, h1311, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1265, h1266, h1310, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1317 | h1317
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1318 | h1318
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1319 | h1319
                    · linarith only [h1266, h1319, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1265, h1319, hlam]
                  · linarith only [h1290, h1318, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1265, h1290, h1317, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1306, hlam, p0_0]
    · linarith only [h1265, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1326 | h1326
    · rcases p0_3 (m.d 1 2) (by simp) with h1327 | h1327
      · rcases p0_3 (m.d 1 3) (by simp) with h1328 | h1328
        · rcases p0_3 (m.d 1 4) (by simp) with h1329 | h1329
          · rcases p0_3 (m.d 1 5) (by simp) with h1330 | h1330
            · rcases p0_3 (m.d 1 6) (by simp) with h1331 | h1331
              · linarith only [h1331, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1333 | h1333
                · linarith only [h1327, h1333, hc01, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                · linarith only [h1333, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1336 | h1336
              · linarith only [h1336, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1338 | h1338
                · linarith only [h1327, h1330, h1338, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1338, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h1329, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1342 | h1342
          · rcases p0_3 (m.d 1 5) (by simp) with h1343 | h1343
            · rcases p0_3 (m.d 1 6) (by simp) with h1344 | h1344
              · linarith only [h1344, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1346 | h1346
                · linarith only [h1327, h1328, h1346, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1346, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1349 | h1349
              · linarith only [h1349, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1351 | h1351
                · linarith only [h1327, h1328, h1351, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1351, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h1342, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1355 | h1355
        · rcases p0_3 (m.d 1 4) (by simp) with h1356 | h1356
          · rcases p0_3 (m.d 1 5) (by simp) with h1357 | h1357
            · rcases p0_3 (m.d 1 6) (by simp) with h1358 | h1358
              · linarith only [h1358, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1360 | h1360
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1361 | h1361
                  · linarith only [h1327, h1355, h1361, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1361, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1326, h1327, h1360, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1365 | h1365
              · linarith only [h1365, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1367 | h1367
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1368 | h1368
                  · linarith only [h1327, h1355, h1368, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1368, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1326, h1327, h1367, hlam, p0_1]
          · linarith only [h1356, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1373 | h1373
          · rcases p0_3 (m.d 1 5) (by simp) with h1374 | h1374
            · rcases p0_3 (m.d 1 6) (by simp) with h1375 | h1375
              · linarith only [h1375, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1377 | h1377
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1378 | h1378
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1379 | h1379
                    · linarith only [h1327, h1379, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1326, h1379, hlam]
                  · linarith only [h1355, h1378, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1326, h1327, h1377, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1384 | h1384
              · linarith only [h1384, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1386 | h1386
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1387 | h1387
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1388 | h1388
                    · linarith only [h1327, h1388, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1326, h1388, hlam]
                  · linarith only [h1355, h1387, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h1326, h1355, h1386, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1373, hlam, p0_0]
    · linarith only [h1326, hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1396 | h1396
    · rcases p0_3 (m.d 1 2) (by simp) with h1397 | h1397
      · linarith only [h1397, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1399 | h1399
        · rcases p0_3 (m.d 1 4) (by simp) with h1400 | h1400
          · rcases p0_3 (m.d 1 5) (by simp) with h1401 | h1401
            · rcases p0_3 (m.d 1 6) (by simp) with h1402 | h1402
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1403 | h1403
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1404 | h1404
                  · linarith only [h1399, h1404, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1404, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1396, h1403, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1408 | h1408
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1409 | h1409
                  · linarith only [h1399, h1409, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1409, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1396, h1408, hlam, p0_1]
            · linarith only [h1401, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1414 | h1414
            · rcases p0_3 (m.d 1 6) (by simp) with h1415 | h1415
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1416 | h1416
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1417 | h1417
                  · linarith only [h1399, h1417, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1417, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1396, h1416, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1421 | h1421
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1422 | h1422
                  · linarith only [h1399, h1422, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1422, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1396, h1421, hlam, p0_1]
            · linarith only [h1414, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1427 | h1427
          · rcases p0_3 (m.d 1 5) (by simp) with h1428 | h1428
            · rcases p0_3 (m.d 1 6) (by simp) with h1429 | h1429
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1430 | h1430
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1431 | h1431
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1432 | h1432
                    · linarith only [h1427, h1432, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1432, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1396, h1399, h1431, hlam, p0_1]
                · linarith only [h1396, h1430, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1437 | h1437
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1438 | h1438
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1439 | h1439
                    · linarith only [h1427, h1439, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1439, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1396, h1399, h1438, hlam, p0_1]
                · linarith only [h1396, h1437, hlam, p0_1]
            · linarith only [h1428, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1445 | h1445
            · rcases p0_3 (m.d 1 6) (by simp) with h1446 | h1446
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1447 | h1447
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1448 | h1448
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1449 | h1449
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1450 | h1450
                      · linarith only [h1450, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1396, h1450, hlam]
                    · linarith only [h1427, h1449, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1396, h1399, h1448, hlam, p0_1]
                · linarith only [h1396, h1447, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1456 | h1456
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1457 | h1457
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1458 | h1458
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1459 | h1459
                      · linarith only [h1459, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1396, h1459, hlam]
                    · linarith only [h1427, h1458, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1396, h1399, h1457, hlam, p0_1]
                · linarith only [h1396, h1456, hlam, p0_1]
            · linarith only [h1445, hlam, p0_0]
    · linarith only [h1396, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1467 | h1467
    · rcases p0_3 (m.d 1 2) (by simp) with h1468 | h1468
      · rcases p0_3 (m.d 1 3) (by simp) with h1469 | h1469
        · linarith only [h1469, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1471 | h1471
          · rcases p0_3 (m.d 1 5) (by simp) with h1472 | h1472
            · rcases p0_3 (m.d 1 6) (by simp) with h1473 | h1473
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1474 | h1474
                · linarith only [h1468, h1474, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1474, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1477 | h1477
                · linarith only [h1468, h1477, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1477, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h1472, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1481 | h1481
            · rcases p0_3 (m.d 1 6) (by simp) with h1482 | h1482
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1483 | h1483
                · linarith only [h1468, h1483, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1483, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1486 | h1486
                · linarith only [h1468, h1486, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1486, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h1481, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1490 | h1490
        · linarith only [h1490, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1492 | h1492
          · rcases p0_3 (m.d 1 5) (by simp) with h1493 | h1493
            · rcases p0_3 (m.d 1 6) (by simp) with h1494 | h1494
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1495 | h1495
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1496 | h1496
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1497 | h1497
                    · linarith only [h1468, h1492, h1497, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1497, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1467, h1496, hlam, p0_1]
                · linarith only [h1467, h1468, h1495, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1502 | h1502
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1503 | h1503
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1504 | h1504
                    · linarith only [h1468, h1492, h1504, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1504, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1467, h1503, hlam, p0_1]
                · linarith only [h1467, h1468, h1502, hlam, p0_1]
            · linarith only [h1493, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1510 | h1510
            · rcases p0_3 (m.d 1 6) (by simp) with h1511 | h1511
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1512 | h1512
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1513 | h1513
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1514 | h1514
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1515 | h1515
                      · linarith only [h1468, h1515, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1467, h1515, hlam]
                    · linarith only [h1492, h1514, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1467, h1513, hlam, p0_1]
                · linarith only [h1467, h1468, h1512, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1521 | h1521
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1522 | h1522
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1523 | h1523
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1524 | h1524
                      · linarith only [h1468, h1524, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1467, h1524, hlam]
                    · linarith only [h1492, h1523, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1467, h1522, hlam, p0_1]
                · linarith only [h1467, h1521, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1510, hlam, p0_0]
    · linarith only [h1467, hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1532 | h1532
    · rcases p0_3 (m.d 1 2) (by simp) with h1533 | h1533
      · rcases p0_3 (m.d 1 3) (by simp) with h1534 | h1534
        · rcases p0_3 (m.d 1 4) (by simp) with h1535 | h1535
          · linarith only [h1535, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1537 | h1537
            · rcases p0_3 (m.d 1 6) (by simp) with h1538 | h1538
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1539 | h1539
                · linarith only [h1533, h1539, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1539, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1542 | h1542
                · linarith only [h1533, h1542, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1542, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h1537, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1546 | h1546
          · linarith only [h1546, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1548 | h1548
            · rcases p0_3 (m.d 1 6) (by simp) with h1549 | h1549
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1550 | h1550
                · linarith only [h1533, h1534, h1550, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1550, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1553 | h1553
                · linarith only [h1533, h1534, h1553, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1553, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h1548, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1557 | h1557
        · rcases p0_3 (m.d 1 4) (by simp) with h1558 | h1558
          · linarith only [h1558, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1560 | h1560
            · rcases p0_3 (m.d 1 6) (by simp) with h1561 | h1561
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1562 | h1562
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1563 | h1563
                  · linarith only [h1533, h1557, h1563, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1563, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1532, h1533, h1562, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1567 | h1567
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1568 | h1568
                  · linarith only [h1533, h1557, h1568, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1568, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1532, h1533, h1567, hlam, p0_1]
            · linarith only [h1560, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1573 | h1573
          · linarith only [h1573, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1575 | h1575
            · rcases p0_3 (m.d 1 6) (by simp) with h1576 | h1576
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1577 | h1577
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1578 | h1578
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1579 | h1579
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1580 | h1580
                      · linarith only [h1533, h1580, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1532, h1580, hlam]
                    · linarith only [h1579, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1532, h1557, h1578, hlam, p0_1]
                · linarith only [h1532, h1533, h1577, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1586 | h1586
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1587 | h1587
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1588 | h1588
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1589 | h1589
                      · linarith only [h1533, h1589, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1532, h1589, hlam]
                    · linarith only [h1588, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1532, h1533, h1587, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1532, h1533, h1586, hlam, p0_1]
            · linarith only [h1575, hlam, p0_0]
    · linarith only [h1532, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1598 | h1598
    · rcases p0_3 (m.d 1 2) (by simp) with h1599 | h1599
      · rcases p0_3 (m.d 1 3) (by simp) with h1600 | h1600
        · rcases p0_3 (m.d 1 4) (by simp) with h1601 | h1601
          · rcases p0_3 (m.d 1 5) (by simp) with h1602 | h1602
            · rcases p0_3 (m.d 1 6) (by simp) with h1603 | h1603
              · linarith only [h1603, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1605 | h1605
                · linarith only [h1599, h1605, hc01, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                · linarith only [h1605, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h1602, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1609 | h1609
            · rcases p0_3 (m.d 1 6) (by simp) with h1610 | h1610
              · linarith only [h1610, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1612 | h1612
                · linarith only [h1599, h1601, h1612, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1612, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h1609, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1616 | h1616
          · rcases p0_3 (m.d 1 5) (by simp) with h1617 | h1617
            · rcases p0_3 (m.d 1 6) (by simp) with h1618 | h1618
              · linarith only [h1618, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1620 | h1620
                · linarith only [h1599, h1600, h1620, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1620, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h1617, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1624 | h1624
            · rcases p0_3 (m.d 1 6) (by simp) with h1625 | h1625
              · linarith only [h1625, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1627 | h1627
                · linarith only [h1599, h1600, h1627, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1627, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h1624, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1631 | h1631
        · rcases p0_3 (m.d 1 4) (by simp) with h1632 | h1632
          · rcases p0_3 (m.d 1 5) (by simp) with h1633 | h1633
            · rcases p0_3 (m.d 1 6) (by simp) with h1634 | h1634
              · linarith only [h1634, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1636 | h1636
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1637 | h1637
                  · linarith only [h1599, h1631, h1637, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1637, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1598, h1599, h1636, hlam, p0_1]
            · linarith only [h1633, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1642 | h1642
            · rcases p0_3 (m.d 1 6) (by simp) with h1643 | h1643
              · linarith only [h1643, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1645 | h1645
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1646 | h1646
                  · linarith only [h1599, h1631, h1646, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1646, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1598, h1599, h1645, hlam, p0_1]
            · linarith only [h1642, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1651 | h1651
          · rcases p0_3 (m.d 1 5) (by simp) with h1652 | h1652
            · rcases p0_3 (m.d 1 6) (by simp) with h1653 | h1653
              · linarith only [h1653, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1655 | h1655
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1656 | h1656
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1657 | h1657
                    · linarith only [h1599, h1651, h1657, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1657, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1598, h1631, h1656, hlam, p0_1]
                · linarith only [h1598, h1599, h1655, hlam, p0_1]
            · linarith only [h1652, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1663 | h1663
            · rcases p0_3 (m.d 1 6) (by simp) with h1664 | h1664
              · linarith only [h1664, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1666 | h1666
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1667 | h1667
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1668 | h1668
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1669 | h1669
                      · linarith only [h1599, h1669, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1598, h1669, hlam]
                    · linarith only [h1651, h1668, hc01, hc15, hlam, hphi, p0_1]
                  · linarith only [h1598, h1631, h1667, hlam, p0_1]
                · linarith only [h1598, h1599, h1666, hlam, p0_1]
            · linarith only [h1663, hlam, p0_0]
    · linarith only [h1598, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1678 | h1678
    · rcases p0_3 (m.d 1 2) (by simp) with h1679 | h1679
      · linarith only [h1679, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1681 | h1681
        · rcases p0_3 (m.d 1 4) (by simp) with h1682 | h1682
          · rcases p0_3 (m.d 1 5) (by simp) with h1683 | h1683
            · rcases p0_3 (m.d 1 6) (by simp) with h1684 | h1684
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1685 | h1685
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1686 | h1686
                  · linarith only [h1681, h1686, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1686, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1678, h1685, hlam, p0_1]
              · linarith only [h1684, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1691 | h1691
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1692 | h1692
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1693 | h1693
                  · linarith only [h1681, h1693, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1693, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1678, h1692, hlam, p0_1]
              · linarith only [h1691, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1698 | h1698
            · rcases p0_3 (m.d 1 6) (by simp) with h1699 | h1699
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1700 | h1700
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1701 | h1701
                  · linarith only [h1681, h1701, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1701, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1678, h1700, hlam, p0_1]
              · linarith only [h1699, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1706 | h1706
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1707 | h1707
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1708 | h1708
                  · linarith only [h1681, h1708, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1708, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1678, h1707, hlam, p0_1]
              · linarith only [h1706, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1713 | h1713
          · rcases p0_3 (m.d 1 5) (by simp) with h1714 | h1714
            · rcases p0_3 (m.d 1 6) (by simp) with h1715 | h1715
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1716 | h1716
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1717 | h1717
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1718 | h1718
                    · linarith only [h1713, h1718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1718, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1678, h1681, h1717, hlam, p0_1]
                · linarith only [h1678, h1716, hlam, p0_1]
              · linarith only [h1715, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1724 | h1724
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1725 | h1725
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1726 | h1726
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1727 | h1727
                    · linarith only [h1713, h1727, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1727, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1678, h1681, h1726, hlam, p0_1]
                · linarith only [h1678, h1725, hlam, p0_1]
              · linarith only [h1724, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1733 | h1733
            · rcases p0_3 (m.d 1 6) (by simp) with h1734 | h1734
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1735 | h1735
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1736 | h1736
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1737 | h1737
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1738 | h1738
                      · linarith only [h1733, h1738, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1738, hc15, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h1678, h1713, h1737, hlam, p0_1]
                  · linarith only [h1678, h1681, h1736, hlam, p0_1]
                · linarith only [h1678, h1735, hlam, p0_1]
              · linarith only [h1734, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1745 | h1745
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1746 | h1746
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1747 | h1747
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1748 | h1748
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1749 | h1749
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1750 | h1750
                        · linarith only [h1750, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1678, h1750, hlam]
                      · linarith only [h1733, h1749, hc01, hc16, hlam, hphi, p0_1]
                    · linarith only [h1678, h1713, h1748, hlam, p0_1]
                  · linarith only [h1678, h1681, h1747, hlam, p0_1]
                · linarith only [h1678, h1746, hlam, p0_1]
              · linarith only [h1745, hlam, p0_0]
    · linarith only [h1678, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1759 | h1759
    · rcases p0_3 (m.d 1 2) (by simp) with h1760 | h1760
      · rcases p0_3 (m.d 1 3) (by simp) with h1761 | h1761
        · linarith only [h1761, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1763 | h1763
          · rcases p0_3 (m.d 1 5) (by simp) with h1764 | h1764
            · rcases p0_3 (m.d 1 6) (by simp) with h1765 | h1765
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1766 | h1766
                · linarith only [h1760, h1766, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1766, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1765, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1770 | h1770
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1771 | h1771
                · linarith only [h1760, h1771, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1771, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1770, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1775 | h1775
            · rcases p0_3 (m.d 1 6) (by simp) with h1776 | h1776
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1777 | h1777
                · linarith only [h1760, h1777, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1777, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1776, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1781 | h1781
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1782 | h1782
                · linarith only [h1760, h1782, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1782, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1781, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1786 | h1786
        · linarith only [h1786, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1788 | h1788
          · rcases p0_3 (m.d 1 5) (by simp) with h1789 | h1789
            · rcases p0_3 (m.d 1 6) (by simp) with h1790 | h1790
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1791 | h1791
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1792 | h1792
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1793 | h1793
                    · linarith only [h1760, h1788, h1793, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1793, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1759, h1792, hlam, p0_1]
                · linarith only [h1759, h1760, h1791, hlam, p0_1]
              · linarith only [h1790, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1799 | h1799
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1800 | h1800
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1801 | h1801
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1802 | h1802
                    · linarith only [h1760, h1788, h1802, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1802, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1759, h1801, hlam, p0_1]
                · linarith only [h1759, h1760, h1800, hlam, p0_1]
              · linarith only [h1799, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1808 | h1808
            · rcases p0_3 (m.d 1 6) (by simp) with h1809 | h1809
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1810 | h1810
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1811 | h1811
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1812 | h1812
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1813 | h1813
                      · linarith only [h1760, h1808, h1813, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1813, hc15, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h1759, h1788, h1812, hlam, p0_1]
                  · linarith only [h1759, h1811, hlam, p0_1]
                · linarith only [h1759, h1760, h1810, hlam, p0_1]
              · linarith only [h1809, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1820 | h1820
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1821 | h1821
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1822 | h1822
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1823 | h1823
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1824 | h1824
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1825 | h1825
                        · linarith only [h1760, h1825, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1759, h1825, hlam]
                      · linarith only [h1808, h1824, hc01, hc16, hlam, hphi, p0_1]
                    · linarith only [h1759, h1788, h1823, hlam, p0_1]
                  · linarith only [h1759, h1822, hlam, p0_1]
                · linarith only [h1759, h1760, h1821, hlam, p0_1]
              · linarith only [h1820, hlam, p0_0]
    · linarith only [h1759, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1834 | h1834
    · rcases p0_3 (m.d 1 2) (by simp) with h1835 | h1835
      · rcases p0_3 (m.d 1 3) (by simp) with h1836 | h1836
        · rcases p0_3 (m.d 1 4) (by simp) with h1837 | h1837
          · linarith only [h1837, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1839 | h1839
            · rcases p0_3 (m.d 1 6) (by simp) with h1840 | h1840
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1841 | h1841
                · linarith only [h1835, h1841, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1841, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1840, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1845 | h1845
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1846 | h1846
                · linarith only [h1835, h1846, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1846, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1845, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1850 | h1850
          · linarith only [h1850, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1852 | h1852
            · rcases p0_3 (m.d 1 6) (by simp) with h1853 | h1853
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1854 | h1854
                · linarith only [h1835, h1836, h1854, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1854, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1853, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1858 | h1858
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1859 | h1859
                · linarith only [h1835, h1836, h1859, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1859, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1858, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1863 | h1863
        · rcases p0_3 (m.d 1 4) (by simp) with h1864 | h1864
          · linarith only [h1864, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1866 | h1866
            · rcases p0_3 (m.d 1 6) (by simp) with h1867 | h1867
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1868 | h1868
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1869 | h1869
                  · linarith only [h1835, h1863, h1869, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1869, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1834, h1835, h1868, hlam, p0_1]
              · linarith only [h1867, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1874 | h1874
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1875 | h1875
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1876 | h1876
                  · linarith only [h1835, h1863, h1876, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1876, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1834, h1835, h1875, hlam, p0_1]
              · linarith only [h1874, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1881 | h1881
          · linarith only [h1881, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1883 | h1883
            · rcases p0_3 (m.d 1 6) (by simp) with h1884 | h1884
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1885 | h1885
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1886 | h1886
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1887 | h1887
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1888 | h1888
                      · linarith only [h1835, h1883, h1888, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1888, hc15, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h1834, h1887, hlam, p0_1]
                  · linarith only [h1834, h1863, h1886, hlam, p0_1]
                · linarith only [h1834, h1835, h1885, hlam, p0_1]
              · linarith only [h1884, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1895 | h1895
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1896 | h1896
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1897 | h1897
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1898 | h1898
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1899 | h1899
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1900 | h1900
                        · linarith only [h1835, h1900, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1834, h1900, hlam]
                      · linarith only [h1883, h1899, hc01, hc16, hlam, hphi, p0_1]
                    · linarith only [h1834, h1898, hlam, p0_1]
                  · linarith only [h1834, h1863, h1897, hlam, p0_1]
                · linarith only [h1834, h1835, h1896, hlam, p0_1]
              · linarith only [h1895, hlam, p0_0]
    · linarith only [h1834, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1909 | h1909
    · rcases p0_3 (m.d 1 2) (by simp) with h1910 | h1910
      · rcases p0_3 (m.d 1 3) (by simp) with h1911 | h1911
        · rcases p0_3 (m.d 1 4) (by simp) with h1912 | h1912
          · rcases p0_3 (m.d 1 5) (by simp) with h1913 | h1913
            · linarith only [h1913, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1915 | h1915
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1916 | h1916
                · linarith only [h1910, h1916, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1916, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1915, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1920 | h1920
            · linarith only [h1920, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1922 | h1922
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1923 | h1923
                · linarith only [h1910, h1912, h1923, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1923, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1922, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1927 | h1927
          · rcases p0_3 (m.d 1 5) (by simp) with h1928 | h1928
            · linarith only [h1928, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1930 | h1930
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1931 | h1931
                · linarith only [h1910, h1911, h1931, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1931, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1930, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1935 | h1935
            · linarith only [h1935, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1937 | h1937
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1938 | h1938
                · linarith only [h1910, h1911, h1938, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1938, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h1937, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1942 | h1942
        · rcases p0_3 (m.d 1 4) (by simp) with h1943 | h1943
          · rcases p0_3 (m.d 1 5) (by simp) with h1944 | h1944
            · linarith only [h1944, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1946 | h1946
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1947 | h1947
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1948 | h1948
                  · linarith only [h1910, h1942, h1948, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1948, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1909, h1910, h1947, hlam, p0_1]
              · linarith only [h1946, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1953 | h1953
            · linarith only [h1953, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1955 | h1955
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1956 | h1956
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1957 | h1957
                  · linarith only [h1910, h1942, h1957, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1957, hc13, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1909, h1910, h1956, hlam, p0_1]
              · linarith only [h1955, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1962 | h1962
          · rcases p0_3 (m.d 1 5) (by simp) with h1963 | h1963
            · linarith only [h1963, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1965 | h1965
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1966 | h1966
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1967 | h1967
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1968 | h1968
                    · linarith only [h1910, h1962, h1968, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1968, hc14, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1909, h1942, h1967, hlam, p0_1]
                · linarith only [h1909, h1910, h1966, hlam, p0_1]
              · linarith only [h1965, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1974 | h1974
            · linarith only [h1974, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1976 | h1976
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1977 | h1977
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1978 | h1978
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1979 | h1979
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1980 | h1980
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1981 | h1981
                        · linarith only [h1910, h1981, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1909, h1981, hlam]
                      · linarith only [h1980, hc01, hc16, hlam, hphi, p0_1]
                    · linarith only [h1909, h1962, h1979, hlam, p0_1]
                  · linarith only [h1909, h1942, h1978, hlam, p0_1]
                · linarith only [h1909, h1910, h1977, hlam, p0_1]
              · linarith only [h1976, hlam, p0_0]
    · linarith only [h1909, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

set_option maxHeartbeats 6006000 in
theorem n8l_sAA8_M_LI_M_LI (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u1elo5 := h1elo (m.d 1 6) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 1 6) (by simp) with h8 | h8
              · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
                · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h5, hlam]
                  · linarith only [h10, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h9, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h14 | h14
                · rcases m.htr 0 1 3 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h5, hlam]
                  · linarith only [h15, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h14, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h19 | h19
              · rcases m.htr 0 1 2 (by decide) (by decide) with h20 | h20
                · rcases m.htr 0 1 3 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, h5, hlam]
                  · linarith only [h21, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h20, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
                  · linarith only [h26, h5, hlam]
                  · linarith only [h26, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h25, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h30 | h30
            · rcases p0_3 (m.d 1 6) (by simp) with h31 | h31
              · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
                · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                  · linarith only [h33, h5, hlam]
                  · linarith only [h33, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h32, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h37 | h37
                · rcases m.htr 0 1 3 (by decide) (by decide) with h38 | h38
                  · linarith only [h38, h5, hlam]
                  · linarith only [h38, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h37, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h42 | h42
              · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
                · rcases m.htr 0 1 3 (by decide) (by decide) with h44 | h44
                  · linarith only [h44, h5, hlam]
                  · linarith only [h44, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h43, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
                · rcases m.htr 0 1 3 (by decide) (by decide) with h49 | h49
                  · linarith only [h49, h5, hlam]
                  · linarith only [h49, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h48, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
          · rcases p0_3 (m.d 1 5) (by simp) with h54 | h54
            · rcases p0_3 (m.d 1 6) (by simp) with h55 | h55
              · rcases m.htr 0 1 2 (by decide) (by decide) with h56 | h56
                · rcases m.htr 0 1 3 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h58 | h58
                    · linarith only [h53, h58, hlam]
                    · linarith only [h58, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h5, h57, hlam, p0_1]
                · linarith only [h56, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 3 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h65 | h65
                    · linarith only [h53, h65, hlam]
                    · linarith only [h65, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h5, h64, hlam, p0_1]
                · linarith only [h63, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h70 | h70
              · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
                · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                    · linarith only [h53, h73, hlam]
                    · linarith only [h73, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h5, h72, hlam, p0_1]
                · linarith only [h71, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h78 | h78
                · rcases m.htr 0 1 3 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h80 | h80
                    · linarith only [h53, h80, hlam]
                    · linarith only [h80, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h5, h79, hlam, p0_1]
                · linarith only [h78, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h85 | h85
            · rcases p0_3 (m.d 1 6) (by simp) with h86 | h86
              · rcases m.htr 0 1 2 (by decide) (by decide) with h87 | h87
                · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
                      · linarith only [h85, h90, hlam]
                      · linarith only [h90, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h53, h89, hlam, p0_1]
                  · linarith only [h5, h88, hlam, p0_1]
                · linarith only [h87, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h96 | h96
                · rcases m.htr 0 1 3 (by decide) (by decide) with h97 | h97
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h99 | h99
                      · linarith only [h85, h99, hlam]
                      · linarith only [h99, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h53, h98, hlam, p0_1]
                  · linarith only [h5, h97, hlam, p0_1]
                · linarith only [h96, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h105 | h105
              · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
                · rcases m.htr 0 1 3 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h110 | h110
                        · linarith only [h105, h110, hlam]
                        · linarith only [h110, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo5]
                      · linarith only [h109, h85, hlam, p0_1]
                    · linarith only [h108, h53, hlam, p0_1]
                  · linarith only [h107, h5, hlam, p0_1]
                · linarith only [h106, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h117 | h117
                · rcases m.htr 0 1 3 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h120 | h120
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h121 | h121
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h122 | h122
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h123 | h123
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h124 | h124
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h125 | h125
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                                    · linarith only [h127, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                                    · linarith only [h127, h5, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
                                    · linarith only [h130, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h130, h5, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
                                  · linarith only [h124, h125, h133, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                                    · linarith only [h135, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h135, h5, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h138 | h138
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h139 | h139
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
                                    · linarith only [h140, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h140, h5, hlam]
                                  · linarith only [h124, h138, h139, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h144 | h144
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
                                    · linarith only [h145, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h145, h5, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                                    · linarith only [h148, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h148, h5, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h151 | h151
                              · linarith only [h122, h123, h151, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h153 | h153
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h154 | h154
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                                    · linarith only [h155, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h155, h5, hlam]
                                  · linarith only [h122, h123, h153, h154, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h159 | h159
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
                                    · linarith only [h160, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h160, h5, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                                    · linarith only [h163, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h163, h5, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h166 | h166
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h167 | h167
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h168 | h168
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                                    · linarith only [h122, h170, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h170, h5, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
                                    · linarith only [h122, h166, h173, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h173, h5, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h176 | h176
                                  · linarith only [h122, h166, h168, h176, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                                    · linarith only [h122, h166, h178, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h178, h5, hlam]
                              · linarith only [h122, h166, h167, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h182 | h182
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h184 | h184
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h185 | h185
                                    · linarith only [h122, h185, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h185, h5, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
                                    · linarith only [h117, h122, h188, hlam]
                                    · linarith only [h188, h5, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
                                  · linarith only [h182, h183, h191, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
                                    · linarith only [h117, h122, h193, hlam]
                                    · linarith only [h193, h5, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h196 | h196
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h197 | h197
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
                                    · linarith only [h117, h122, h198, hlam]
                                    · linarith only [h198, h5, hlam]
                                  · linarith only [h182, h196, h197, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h202 | h202
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h203 | h203
                                    · linarith only [h117, h122, h203, hlam]
                                    · linarith only [h203, h5, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
                                    · linarith only [h117, h122, h206, hlam]
                                    · linarith only [h206, h5, hlam]
                        · linarith only [h105, h121, hlam, p0_1]
                      · linarith only [h120, h85, hlam, p0_1]
                    · linarith only [h119, h53, hlam, p0_1]
                  · linarith only [h118, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h117, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h215 | h215
    · rcases p0_3 (m.d 1 2) (by simp) with h216 | h216
      · rcases p0_3 (m.d 1 3) (by simp) with h217 | h217
        · linarith only [h217, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h219 | h219
          · rcases p0_3 (m.d 1 5) (by simp) with h220 | h220
            · rcases p0_3 (m.d 1 6) (by simp) with h221 | h221
              · rcases m.htr 0 1 2 (by decide) (by decide) with h222 | h222
                · linarith only [h216, h222, hlam]
                · linarith only [h222, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h225 | h225
                · linarith only [h216, h225, hlam]
                · linarith only [h225, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h228 | h228
              · rcases m.htr 0 1 2 (by decide) (by decide) with h229 | h229
                · linarith only [h216, h229, hlam]
                · linarith only [h229, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h232 | h232
                · linarith only [h216, h232, hlam]
                · linarith only [h232, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h235 | h235
            · rcases p0_3 (m.d 1 6) (by simp) with h236 | h236
              · rcases m.htr 0 1 2 (by decide) (by decide) with h237 | h237
                · linarith only [h216, h237, hlam]
                · linarith only [h237, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h240 | h240
                · linarith only [h216, h240, hlam]
                · linarith only [h240, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h243 | h243
              · rcases m.htr 0 1 2 (by decide) (by decide) with h244 | h244
                · linarith only [h216, h244, hlam]
                · linarith only [h244, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h247 | h247
                · linarith only [h216, h247, hlam]
                · linarith only [h247, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h250 | h250
        · linarith only [h250, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h252 | h252
          · rcases p0_3 (m.d 1 5) (by simp) with h253 | h253
            · rcases p0_3 (m.d 1 6) (by simp) with h254 | h254
              · rcases m.htr 0 1 2 (by decide) (by decide) with h255 | h255
                · rcases m.htr 0 1 3 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h257 | h257
                    · linarith only [h252, h257, hlam]
                    · linarith only [h216, h257, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h256, hlam, p0_0]
                · linarith only [h216, h255, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h262 | h262
                · rcases m.htr 0 1 3 (by decide) (by decide) with h263 | h263
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h264 | h264
                    · linarith only [h252, h264, hlam]
                    · linarith only [h216, h264, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h263, hlam, p0_0]
                · linarith only [h216, h262, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h269 | h269
              · rcases m.htr 0 1 2 (by decide) (by decide) with h270 | h270
                · rcases m.htr 0 1 3 (by decide) (by decide) with h271 | h271
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h272 | h272
                    · linarith only [h252, h272, hlam]
                    · linarith only [h216, h272, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h271, hlam, p0_0]
                · linarith only [h216, h270, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h277 | h277
                · rcases m.htr 0 1 3 (by decide) (by decide) with h278 | h278
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h279 | h279
                    · linarith only [h252, h279, hlam]
                    · linarith only [h216, h279, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h278, hlam, p0_0]
                · linarith only [h216, h277, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h284 | h284
            · rcases p0_3 (m.d 1 6) (by simp) with h285 | h285
              · rcases m.htr 0 1 2 (by decide) (by decide) with h286 | h286
                · rcases m.htr 0 1 3 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h288 | h288
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h289 | h289
                      · linarith only [h284, h289, hlam]
                      · linarith only [h216, h289, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h252, h288, hlam, p0_1]
                  · linarith only [h287, hlam, p0_0]
                · linarith only [h216, h286, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h295 | h295
                · rcases m.htr 0 1 3 (by decide) (by decide) with h296 | h296
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h297 | h297
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h298 | h298
                      · linarith only [h284, h298, hlam]
                      · linarith only [h216, h298, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h252, h297, hlam, p0_1]
                  · linarith only [h296, hlam, p0_0]
                · linarith only [h216, h295, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h304 | h304
              · rcases m.htr 0 1 2 (by decide) (by decide) with h305 | h305
                · rcases m.htr 0 1 3 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h308 | h308
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h309 | h309
                        · linarith only [h304, h309, hlam]
                        · linarith only [h216, h309, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo5]
                      · linarith only [h284, h308, hlam, p0_1]
                    · linarith only [h252, h307, hlam, p0_1]
                  · linarith only [h306, hlam, p0_0]
                · linarith only [h216, h305, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h316 | h316
                · rcases m.htr 0 1 3 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h320 | h320
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h321 | h321
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h322 | h322
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h323 | h323
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h324 | h324
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h325 | h325
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                                    · linarith only [h216, h326, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                                      · linarith only [h326, h328, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
                                        · linarith only [h326, h330, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h332 | h332
                                          · linarith only [h326, h332, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h334 | h334
                                            · linarith only [h334, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h334, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
                                    · linarith only [h216, h337, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h339 | h339
                                      · linarith only [h337, h339, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h341 | h341
                                        · linarith only [h337, h341, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h343 | h343
                                          · linarith only [h337, h343, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
                                            · linarith only [h345, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h345, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
                                  · linarith only [h323, h324, h348, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
                                    · linarith only [h216, h350, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h352 | h352
                                      · linarith only [h350, h352, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h354 | h354
                                        · linarith only [h350, h354, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h356 | h356
                                          · linarith only [h350, h356, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h358 | h358
                                            · linarith only [h358, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h358, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h361 | h361
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h362 | h362
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                                    · linarith only [h216, h363, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                                      · linarith only [h363, h365, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
                                        · linarith only [h363, h367, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h369 | h369
                                          · linarith only [h363, h369, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                                            · linarith only [h323, h371, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h371, hlam]
                                  · linarith only [h323, h361, h362, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h375 | h375
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
                                    · linarith only [h216, h376, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h378 | h378
                                      · linarith only [h376, h378, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h380 | h380
                                        · linarith only [h376, h380, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h382 | h382
                                          · linarith only [h376, h382, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                                            · linarith only [h323, h384, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h384, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h387 | h387
                                    · linarith only [h216, h387, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h389 | h389
                                      · linarith only [h387, h389, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                                        · linarith only [h387, h391, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h393 | h393
                                          · linarith only [h387, h393, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h395 | h395
                                            · linarith only [h395, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h395, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h398 | h398
                              · linarith only [h321, h322, h398, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h400 | h400
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h401 | h401
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h402 | h402
                                    · linarith only [h216, h402, hlam]
                                    · linarith only [h321, h322, h402, hc12, hc24, hlam, hphi]
                                  · linarith only [h321, h322, h400, h401, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h406 | h406
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h407 | h407
                                    · linarith only [h216, h407, hlam]
                                    · linarith only [h321, h322, h407, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h410 | h410
                                    · linarith only [h216, h410, hlam]
                                    · linarith only [h321, h322, h406, h410, hc12, hc45, hlam, hphi, ht23, ht34]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h413 | h413
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h414 | h414
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h416 | h416
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
                                    · linarith only [h216, h417, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h419 | h419
                                      · linarith only [h417, h419, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · linarith only [h321, h413, h419, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h422 | h422
                                    · linarith only [h216, h422, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h424 | h424
                                      · linarith only [h422, h424, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · linarith only [h321, h413, h424, hc12, hc23, hlam, hphi]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                                  · linarith only [h321, h413, h415, h427, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h429 | h429
                                    · linarith only [h216, h429, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h431 | h431
                                      · linarith only [h429, h431, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · linarith only [h321, h413, h415, h431, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h321, h413, h414, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h435 | h435
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h436 | h436
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h437 | h437
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h438 | h438
                                    · linarith only [h216, h438, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h440 | h440
                                      · linarith only [h413, h438, h440, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h442 | h442
                                        · linarith only [h438, h442, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h444 | h444
                                          · linarith only [h438, h444, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h446 | h446
                                            · linarith only [h446, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h446, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h449 | h449
                                    · linarith only [h216, h449, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
                                      · linarith only [h413, h449, h451, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                                        · linarith only [h449, h453, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h455 | h455
                                          · linarith only [h449, h455, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h457 | h457
                                            · linarith only [h457, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h457, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h460 | h460
                                  · linarith only [h435, h436, h460, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                                    · linarith only [h216, h462, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h464 | h464
                                      · linarith only [h413, h462, h464, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
                                        · linarith only [h462, h466, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h468 | h468
                                          · linarith only [h462, h468, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h470 | h470
                                            · linarith only [h470, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h470, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h473 | h473
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h474 | h474
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
                                    · linarith only [h216, h475, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h477 | h477
                                      · linarith only [h475, h477, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
                                        · linarith only [h475, h479, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h481 | h481
                                          · linarith only [h475, h481, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h483 | h483
                                            · linarith only [h435, h473, h483, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h483, hlam]
                                  · linarith only [h435, h473, h474, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h487 | h487
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                                    · linarith only [h216, h488, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                                      · linarith only [h413, h488, h490, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                                        · linarith only [h488, h492, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h494 | h494
                                          · linarith only [h488, h494, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h496 | h496
                                            · linarith only [h321, h435, h496, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h252, h496, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
                                    · linarith only [h216, h499, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h501 | h501
                                      · linarith only [h316, h413, h501, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
                                        · linarith only [h499, h503, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h505 | h505
                                          · linarith only [h252, h501, h505, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h507 | h507
                                            · linarith only [h317, h435, h507, hlam]
                                            · linarith only [h252, h507, hlam]
                        · linarith only [h304, h320, hlam, p0_1]
                      · linarith only [h284, h319, hlam, p0_1]
                    · linarith only [h318, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h317, hlam, p0_0]
                · linarith only [h216, h316, hlam, p0_1]
    · linarith only [h215, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h516 | h516
    · rcases p0_3 (m.d 1 2) (by simp) with h517 | h517
      · rcases p0_3 (m.d 1 3) (by simp) with h518 | h518
        · rcases p0_3 (m.d 1 4) (by simp) with h519 | h519
          · linarith only [h519, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h521 | h521
            · rcases p0_3 (m.d 1 6) (by simp) with h522 | h522
              · rcases m.htr 0 1 2 (by decide) (by decide) with h523 | h523
                · linarith only [h517, h523, hlam]
                · linarith only [h523, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h526 | h526
                · linarith only [h517, h526, hlam]
                · linarith only [h526, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h529 | h529
              · rcases m.htr 0 1 2 (by decide) (by decide) with h530 | h530
                · linarith only [h517, h530, hlam]
                · linarith only [h530, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h533 | h533
                · linarith only [h517, h533, hlam]
                · linarith only [h533, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h536 | h536
          · linarith only [h536, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h538 | h538
            · rcases p0_3 (m.d 1 6) (by simp) with h539 | h539
              · rcases m.htr 0 1 2 (by decide) (by decide) with h540 | h540
                · linarith only [h517, h540, hlam]
                · linarith only [h518, h540, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h543 | h543
                · linarith only [h517, h543, hlam]
                · linarith only [h518, h543, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h546 | h546
              · rcases m.htr 0 1 2 (by decide) (by decide) with h547 | h547
                · linarith only [h517, h547, hlam]
                · linarith only [h518, h547, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h550 | h550
                · linarith only [h517, h550, hlam]
                · linarith only [h518, h550, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h553 | h553
        · rcases p0_3 (m.d 1 4) (by simp) with h554 | h554
          · linarith only [h554, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h556 | h556
            · rcases p0_3 (m.d 1 6) (by simp) with h557 | h557
              · rcases m.htr 0 1 2 (by decide) (by decide) with h558 | h558
                · rcases m.htr 0 1 3 (by decide) (by decide) with h559 | h559
                  · linarith only [h553, h559, hlam]
                  · linarith only [h517, h559, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h517, h558, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h563 | h563
                · rcases m.htr 0 1 3 (by decide) (by decide) with h564 | h564
                  · linarith only [h553, h564, hlam]
                  · linarith only [h517, h564, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h517, h563, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h568 | h568
              · rcases m.htr 0 1 2 (by decide) (by decide) with h569 | h569
                · rcases m.htr 0 1 3 (by decide) (by decide) with h570 | h570
                  · linarith only [h553, h570, hlam]
                  · linarith only [h517, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h517, h569, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h574 | h574
                · rcases m.htr 0 1 3 (by decide) (by decide) with h575 | h575
                  · linarith only [h553, h575, hlam]
                  · linarith only [h517, h575, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h517, h574, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h579 | h579
          · linarith only [h579, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h581 | h581
            · rcases p0_3 (m.d 1 6) (by simp) with h582 | h582
              · rcases m.htr 0 1 2 (by decide) (by decide) with h583 | h583
                · rcases m.htr 0 1 3 (by decide) (by decide) with h584 | h584
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h585 | h585
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h586 | h586
                      · linarith only [h581, h586, hlam]
                      · linarith only [h517, h586, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h585, hlam, p0_0]
                  · linarith only [h553, h584, hlam, p0_1]
                · linarith only [h517, h583, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h592 | h592
                · rcases m.htr 0 1 3 (by decide) (by decide) with h593 | h593
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h594 | h594
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h595 | h595
                      · linarith only [h581, h595, hlam]
                      · linarith only [h517, h595, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h594, hlam, p0_0]
                  · linarith only [h553, h593, hlam, p0_1]
                · linarith only [h517, h592, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h601 | h601
              · rcases m.htr 0 1 2 (by decide) (by decide) with h602 | h602
                · rcases m.htr 0 1 3 (by decide) (by decide) with h603 | h603
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h604 | h604
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h605 | h605
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h606 | h606
                        · linarith only [h601, h606, hlam]
                        · linarith only [h517, h606, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo5]
                      · linarith only [h581, h605, hlam, p0_1]
                    · linarith only [h604, hlam, p0_0]
                  · linarith only [h553, h603, hlam, p0_1]
                · linarith only [h517, h602, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h613 | h613
                · rcases m.htr 0 1 3 (by decide) (by decide) with h614 | h614
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h615 | h615
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h616 | h616
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h617 | h617
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h618 | h618
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h619 | h619
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h620 | h620
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h621 | h621
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h622 | h622
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h623 | h623
                                    · linarith only [h517, h623, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h625 | h625
                                      · linarith only [h517, h625, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h627 | h627
                                        · linarith only [h618, h623, h627, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h629 | h629
                                          · linarith only [h625, h629, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h631 | h631
                                            · linarith only [h553, h631, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h633 | h633
                                              · linarith only [h613, h618, h620, h631, h633, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h635 | h635
                                                · linarith only [h613, h618, h620, h631, h635, hc36, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h637 | h637
                                                  · linarith only [h637, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · linarith only [h581, h637, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h640 | h640
                                    · linarith only [h517, h640, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h642 | h642
                                      · linarith only [h517, h642, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h644 | h644
                                        · linarith only [h613, h618, h640, h644, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h646 | h646
                                          · linarith only [h613, h618, h640, h646, hc26, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h648 | h648
                                            · linarith only [h553, h648, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h650 | h650
                                              · linarith only [h613, h618, h620, h648, h650, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h652 | h652
                                                · linarith only [h613, h618, h620, h648, h652, hc36, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h654 | h654
                                                  · linarith only [h622, h654, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                                  · linarith only [h581, h654, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h657 | h657
                                  · linarith only [h620, h621, h657, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                                    · linarith only [h517, h659, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h661 | h661
                                      · linarith only [h517, h661, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h663 | h663
                                        · linarith only [h661, h663, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h665 | h665
                                          · linarith only [h661, h665, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                                            · linarith only [h553, h667, hlam]
                                            · linarith only [h620, h621, h659, h667, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h670 | h670
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h671 | h671
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
                                    · linarith only [h517, h672, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h674 | h674
                                      · linarith only [h517, h674, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h676 | h676
                                        · linarith only [h674, h676, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h678 | h678
                                          · linarith only [h674, h678, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h680 | h680
                                            · linarith only [h553, h680, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h682 | h682
                                              · linarith only [h680, h682, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                              · linarith only [h620, h670, h672, h682, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h620, h670, h671, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h686 | h686
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h687 | h687
                                    · linarith only [h517, h687, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h689 | h689
                                      · linarith only [h517, h689, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h691 | h691
                                        · linarith only [h613, h618, h687, h691, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h693 | h693
                                          · linarith only [h613, h618, h687, h693, hc26, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h695 | h695
                                            · linarith only [h553, h695, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h697 | h697
                                              · linarith only [h670, h695, h697, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h699 | h699
                                                · linarith only [h695, h699, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h701 | h701
                                                  · linarith only [h701, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · linarith only [h581, h701, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                                    · linarith only [h517, h704, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h706 | h706
                                      · linarith only [h517, h706, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h708 | h708
                                        · linarith only [h706, h708, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h710 | h710
                                          · linarith only [h706, h710, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h712 | h712
                                            · linarith only [h553, h712, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h714 | h714
                                              · linarith only [h670, h712, h714, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h716 | h716
                                                · linarith only [h712, h716, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h718 | h718
                                                  · linarith only [h686, h718, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                                  · linarith only [h581, h718, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h721 | h721
                              · linarith only [h618, h619, h721, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h723 | h723
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h724 | h724
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h725 | h725
                                    · linarith only [h517, h725, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h618, h619, h725, hc12, hc24, hlam, hphi]
                                  · linarith only [h618, h619, h723, h724, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h729 | h729
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
                                    · linarith only [h517, h730, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h618, h619, h730, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
                                    · linarith only [h517, h733, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h618, h619, h733, hc12, hc24, hlam, hphi]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h736 | h736
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h737 | h737
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h738 | h738
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h739 | h739
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
                                    · linarith only [h517, h740, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
                                      · linarith only [h517, h742, hlam]
                                      · linarith only [h618, h736, h742, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h745 | h745
                                    · linarith only [h618, h736, h745, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo1]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h747 | h747
                                      · linarith only [h517, h747, hlam]
                                      · linarith only [h618, h736, h747, hc12, hc23, hlam, hphi]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h750 | h750
                                  · linarith only [h618, h736, h738, h750, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h752 | h752
                                    · linarith only [h517, h752, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h754 | h754
                                      · linarith only [h517, h754, hlam]
                                      · linarith only [h618, h736, h738, h754, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h618, h736, h737, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h758 | h758
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h759 | h759
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h760 | h760
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
                                    · linarith only [h517, h618, h761, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h763 | h763
                                      · linarith only [h517, h763, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h765 | h765
                                        · linarith only [h763, h765, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h767 | h767
                                          · linarith only [h763, h767, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h769 | h769
                                            · linarith only [h553, h769, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h771 | h771
                                              · linarith only [h769, h771, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h773 | h773
                                                · linarith only [h769, h773, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h775 | h775
                                                  · linarith only [h775, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · linarith only [h581, h775, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h778 | h778
                                    · linarith only [h517, h618, h778, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h780 | h780
                                      · linarith only [h517, h780, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h782 | h782
                                        · linarith only [h780, h782, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h784 | h784
                                          · linarith only [h780, h784, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
                                            · linarith only [h553, h786, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h788 | h788
                                              · linarith only [h786, h788, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h790 | h790
                                                · linarith only [h786, h790, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h792 | h792
                                                  · linarith only [h758, h760, h778, h786, h792, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                                  · linarith only [h581, h792, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h795 | h795
                                  · linarith only [h758, h759, h795, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h797 | h797
                                    · linarith only [h613, h618, h797, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h799 | h799
                                      · linarith only [h517, h799, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h801 | h801
                                        · linarith only [h799, h801, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h803 | h803
                                          · linarith only [h799, h803, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h805 | h805
                                            · linarith only [h553, h805, hlam]
                                            · linarith only [h758, h759, h797, h805, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h808 | h808
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h809 | h809
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h810 | h810
                                    · linarith only [h517, h618, h810, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h812 | h812
                                      · linarith only [h517, h812, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h814 | h814
                                        · linarith only [h553, h810, h814, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h816 | h816
                                          · linarith only [h553, h810, h816, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h818 | h818
                                            · linarith only [h553, h818, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h820 | h820
                                              · linarith only [h818, h820, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                              · linarith only [h758, h808, h810, h820, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h758, h808, h809, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h824 | h824
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
                                    · linarith only [h517, h618, h825, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h827 | h827
                                      · linarith only [h517, h827, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h829 | h829
                                        · linarith only [h827, h829, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h831 | h831
                                          · linarith only [h827, h831, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h833 | h833
                                            · linarith only [h553, h833, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h835 | h835
                                              · linarith only [h618, h808, h833, h835, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h837 | h837
                                                · linarith only [h833, h837, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h839 | h839
                                                  · linarith only [h839, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · linarith only [h581, h839, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h842 | h842
                                    · linarith only [h517, h842, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h844 | h844
                                      · linarith only [h517, h844, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h846 | h846
                                        · linarith only [h553, h842, h846, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h848 | h848
                                          · linarith only [h553, h842, h848, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h850 | h850
                                            · linarith only [h553, h850, hlam]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h852 | h852
                                              · linarith only [h808, h850, h852, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h854 | h854
                                                · linarith only [h850, h854, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h856 | h856
                                                  · linarith only [h824, h856, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                                  · linarith only [h581, h856, hlam]
                        · linarith only [h601, h617, hlam, p0_1]
                      · linarith only [h616, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h615, hlam, p0_0]
                  · linarith only [h614, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h517, h613, hlam, p0_1]
    · linarith only [h516, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h865 | h865
    · rcases p0_3 (m.d 1 2) (by simp) with h866 | h866
      · rcases p0_3 (m.d 1 3) (by simp) with h867 | h867
        · rcases p0_3 (m.d 1 4) (by simp) with h868 | h868
          · rcases p0_3 (m.d 1 5) (by simp) with h869 | h869
            · linarith only [h869, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h871 | h871
              · rcases m.htr 0 1 2 (by decide) (by decide) with h872 | h872
                · linarith only [h866, h872, hlam]
                · linarith only [h872, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h875 | h875
                · linarith only [h866, h875, hlam]
                · linarith only [h875, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h878 | h878
            · linarith only [h878, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h880 | h880
              · rcases m.htr 0 1 2 (by decide) (by decide) with h881 | h881
                · linarith only [h866, h881, hlam]
                · linarith only [h868, h881, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h884 | h884
                · linarith only [h866, h884, hlam]
                · linarith only [h868, h884, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h887 | h887
          · rcases p0_3 (m.d 1 5) (by simp) with h888 | h888
            · linarith only [h888, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h890 | h890
              · rcases m.htr 0 1 2 (by decide) (by decide) with h891 | h891
                · linarith only [h866, h891, hlam]
                · linarith only [h867, h891, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h894 | h894
                · linarith only [h866, h894, hlam]
                · linarith only [h867, h894, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h897 | h897
            · linarith only [h897, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h899 | h899
              · rcases m.htr 0 1 2 (by decide) (by decide) with h900 | h900
                · linarith only [h866, h900, hlam]
                · linarith only [h867, h900, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h903 | h903
                · linarith only [h866, h903, hlam]
                · linarith only [h867, h903, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h906 | h906
        · rcases p0_3 (m.d 1 4) (by simp) with h907 | h907
          · rcases p0_3 (m.d 1 5) (by simp) with h908 | h908
            · linarith only [h908, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h910 | h910
              · rcases m.htr 0 1 2 (by decide) (by decide) with h911 | h911
                · rcases m.htr 0 1 3 (by decide) (by decide) with h912 | h912
                  · linarith only [h906, h912, hlam]
                  · linarith only [h866, h912, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h866, h911, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h916 | h916
                · rcases m.htr 0 1 3 (by decide) (by decide) with h917 | h917
                  · linarith only [h906, h917, hlam]
                  · linarith only [h866, h917, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h866, h916, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h921 | h921
            · linarith only [h921, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h923 | h923
              · rcases m.htr 0 1 2 (by decide) (by decide) with h924 | h924
                · rcases m.htr 0 1 3 (by decide) (by decide) with h925 | h925
                  · linarith only [h906, h925, hlam]
                  · linarith only [h866, h925, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h866, h924, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h929 | h929
                · rcases m.htr 0 1 3 (by decide) (by decide) with h930 | h930
                  · linarith only [h906, h930, hlam]
                  · linarith only [h866, h930, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h866, h929, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h934 | h934
          · rcases p0_3 (m.d 1 5) (by simp) with h935 | h935
            · linarith only [h935, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h937 | h937
              · rcases m.htr 0 1 2 (by decide) (by decide) with h938 | h938
                · rcases m.htr 0 1 3 (by decide) (by decide) with h939 | h939
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h940 | h940
                    · linarith only [h934, h940, hlam]
                    · linarith only [h866, h940, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h906, h939, hlam, p0_1]
                · linarith only [h866, h938, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h945 | h945
                · rcases m.htr 0 1 3 (by decide) (by decide) with h946 | h946
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h947 | h947
                    · linarith only [h934, h947, hlam]
                    · linarith only [h866, h947, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h906, h946, hlam, p0_1]
                · linarith only [h866, h945, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h952 | h952
            · linarith only [h952, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h954 | h954
              · rcases m.htr 0 1 2 (by decide) (by decide) with h955 | h955
                · rcases m.htr 0 1 3 (by decide) (by decide) with h956 | h956
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h957 | h957
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h958 | h958
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h959 | h959
                        · linarith only [h954, h959, hlam]
                        · linarith only [h866, h959, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo5]
                      · linarith only [h958, hlam, p0_0]
                    · linarith only [h934, h957, hlam, p0_1]
                  · linarith only [h906, h956, hlam, p0_1]
                · linarith only [h866, h955, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h966 | h966
                · rcases m.htr 0 1 3 (by decide) (by decide) with h967 | h967
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h968 | h968
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h969 | h969
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h970 | h970
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h971 | h971
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h972 | h972
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h973 | h973
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h974 | h974
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h975 | h975
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h976 | h976
                                    · linarith only [h866, h976, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h978 | h978
                                      · linarith only [h971, h976, h978, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h980 | h980
                                        · linarith only [h866, h980, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h982 | h982
                                          · linarith only [h966, h971, h976, h982, hc26, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h984 | h984
                                            · linarith only [h906, h984, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h986 | h986
                                              · linarith only [h906, h986, hlam]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h988 | h988
                                                · linarith only [h966, h971, h973, h984, h988, hc36, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h990 | h990
                                                  · linarith only [h934, h990, hlam]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h992 | h992
                                                    · linarith only [h966, h971, h973, h975, h990, h992, hc46, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h994 | h994
                                                      · linarith only [h994, hc56, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                      · linarith only [h954, h994, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h997 | h997
                                    · linarith only [h866, h997, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h999 | h999
                                      · linarith only [h866, h999, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1001 | h1001
                                        · linarith only [h1001, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1003 | h1003
                                          · linarith only [h1003, h966, h971, h997, hc26, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1005 | h1005
                                            · linarith only [h1005, h906, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1007 | h1007
                                              · linarith only [h1007, h906, hlam]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1009 | h1009
                                                · linarith only [h1005, h1009, h966, h971, h973, hc36, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1011 | h1011
                                                  · linarith only [h1011, h934, hlam]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1013 | h1013
                                                    · linarith only [h1011, h1013, hc46, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1015 | h1015
                                                      · linarith only [h1015, hc56, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                      · linarith only [h1015, h954, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1018 | h1018
                                  · linarith only [h1018, h973, h974, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1020 | h1020
                                    · linarith only [h1020, h866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1022 | h1022
                                      · linarith only [h1022, h866, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1024 | h1024
                                        · linarith only [h1024, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1026 | h1026
                                          · linarith only [h1020, h1026, h966, h971, hc26, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1028 | h1028
                                            · linarith only [h1028, h906, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h1028, h973, h974, hc13, hc35, hlam, hphi]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1031 | h1031
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1032 | h1032
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1033 | h1033
                                    · linarith only [h1033, h866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1035 | h1035
                                      · linarith only [h1035, h866, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1037 | h1037
                                        · linarith only [h1037, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1039 | h1039
                                          · linarith only [h1037, h1039, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1041 | h1041
                                            · linarith only [h1041, h906, h973, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1043 | h1043
                                              · linarith only [h1043, h906, hlam]
                                              · linarith only [h1031, h1033, h1043, h973, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h1031, h1032, h973, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1047 | h1047
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1048 | h1048
                                    · linarith only [h1048, h866, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1050 | h1050
                                      · linarith only [h1048, h1050, h966, h971, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1052 | h1052
                                        · linarith only [h1052, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1054 | h1054
                                          · linarith only [h1048, h1054, h966, h971, hc26, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1056 | h1056
                                            · linarith only [h1056, h906, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1058 | h1058
                                              · linarith only [h1058, h906, hlam]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1060 | h1060
                                                · linarith only [h1056, h1060, h934, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1062 | h1062
                                                  · linarith only [h1062, h934, hlam]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1064 | h1064
                                                    · linarith only [h1047, h1062, h1064, h966, h972, hc46, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1066 | h1066
                                                      · linarith only [h1066, hc56, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                      · linarith only [h1066, h954, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1069 | h1069
                                    · linarith only [h1069, h866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1071 | h1071
                                      · linarith only [h1069, h1071, h966, h971, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1073 | h1073
                                        · linarith only [h1073, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1075 | h1075
                                          · linarith only [h1069, h1075, h966, h971, hc26, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1077 | h1077
                                            · linarith only [h1077, h906, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1079 | h1079
                                              · linarith only [h1079, h906, hlam]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1081 | h1081
                                                · linarith only [h1077, h1081, h934, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1083 | h1083
                                                  · linarith only [h1083, h934, hlam]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1085 | h1085
                                                    · linarith only [h1083, h1085, hc46, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1087 | h1087
                                                      · linarith only [h1087, hc56, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                      · linarith only [h1087, h954, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1090 | h1090
                              · linarith only [h1090, h971, h972, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1092 | h1092
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1093 | h1093
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1094 | h1094
                                    · linarith only [h1094, h866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h1094, h971, h972, hc12, hc24, hlam, hphi]
                                  · linarith only [h1092, h1093, h971, h972, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1098 | h1098
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1099 | h1099
                                    · linarith only [h1099, h866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h1099, h971, h972, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1102 | h1102
                                    · linarith only [h1102, h866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h1098, h1102, h971, h972, hc12, hc45, hlam, hphi, ht23, ht34]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1105 | h1105
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1106 | h1106
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1107 | h1107
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1108 | h1108
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1109 | h1109
                                    · linarith only [h1105, h1109, h971, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo1]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1111 | h1111
                                      · linarith only [h1109, h1111, h906, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · linarith only [h1105, h1111, h971, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1114 | h1114
                                    · linarith only [h1105, h1114, h971, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo1]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1116 | h1116
                                      · linarith only [h1114, h1116, h906, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · linarith only [h1105, h1116, h971, hc12, hc23, hlam, hphi]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1119 | h1119
                                  · linarith only [h1105, h1107, h1119, h971, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1121 | h1121
                                    · linarith only [h1121, h866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1123 | h1123
                                      · linarith only [h1121, h1123, h906, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · linarith only [h1105, h1107, h1123, h971, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1105, h1106, h971, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1127 | h1127
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1128 | h1128
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1129 | h1129
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1130 | h1130
                                    · linarith only [h1130, h866, h971, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1132 | h1132
                                      · linarith only [h1105, h1132, h866, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1134 | h1134
                                        · linarith only [h1134, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1136 | h1136
                                          · linarith only [h1130, h1136, h906, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1138 | h1138
                                            · linarith only [h1138, h906, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1140 | h1140
                                              · linarith only [h1140, h906, hlam]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1142 | h1142
                                                · linarith only [h1127, h1138, h1142, h967, hc36, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1144 | h1144
                                                  · linarith only [h1144, h934, hlam]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1146 | h1146
                                                    · linarith only [h1127, h1129, h1144, h1146, h967, hc46, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1148 | h1148
                                                      · linarith only [h1148, hc56, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                      · linarith only [h1148, h954, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1151 | h1151
                                    · linarith only [h1151, h866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1153 | h1153
                                      · linarith only [h1105, h1153, h866, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1155 | h1155
                                        · linarith only [h1155, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1157 | h1157
                                          · linarith only [h1155, h1157, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1159 | h1159
                                            · linarith only [h1159, h906, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1161 | h1161
                                              · linarith only [h1161, h906, hlam]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1163 | h1163
                                                · linarith only [h1127, h1159, h1163, h967, hc36, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1165 | h1165
                                                  · linarith only [h1165, h934, hlam]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1167 | h1167
                                                    · linarith only [h1165, h1167, hc46, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1169 | h1169
                                                      · linarith only [h1169, hc56, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                      · linarith only [h1169, h954, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1172 | h1172
                                  · linarith only [h1127, h1128, h1172, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1174 | h1174
                                    · linarith only [h1174, h866, h971, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1176 | h1176
                                      · linarith only [h1105, h1176, h966, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1178 | h1178
                                        · linarith only [h1178, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1180 | h1180
                                          · linarith only [h1174, h1180, h906, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1182 | h1182
                                            · linarith only [h1182, h906, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h1127, h1128, h1174, h1182, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1185 | h1185
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1186 | h1186
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1187 | h1187
                                    · linarith only [h1187, h866, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1189 | h1189
                                      · linarith only [h1105, h1127, h1187, h1189, h906, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1191 | h1191
                                        · linarith only [h1191, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1193 | h1193
                                          · linarith only [h1187, h1193, h906, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1195 | h1195
                                            · linarith only [h1195, h906, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1197 | h1197
                                              · linarith only [h1197, h906, hlam]
                                              · linarith only [h1127, h1185, h1187, h1197, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h1127, h1185, h1186, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1201 | h1201
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1202 | h1202
                                    · linarith only [h1202, h866, h971, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1204 | h1204
                                      · linarith only [h1105, h1204, h866, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1206 | h1206
                                        · linarith only [h1206, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1208 | h1208
                                          · linarith only [h1202, h1208, h906, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1210 | h1210
                                            · linarith only [h1127, h1210, h906, h971, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1212 | h1212
                                              · linarith only [h1212, h906, hlam]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1214 | h1214
                                                · linarith only [h1212, h1214, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1216 | h1216
                                                  · linarith only [h1216, h934, hlam]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1218 | h1218
                                                    · linarith only [h1216, h1218, hc46, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1220 | h1220
                                                      · linarith only [h1220, hc56, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                      · linarith only [h1220, h954, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1223 | h1223
                                    · linarith only [h1223, h966, h971, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1225 | h1225
                                      · linarith only [h1105, h1225, h866, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1227 | h1227
                                        · linarith only [h1227, h866, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1229 | h1229
                                          · linarith only [h1223, h1229, h906, hc26, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1231 | h1231
                                            · linarith only [h1231, h906, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1233 | h1233
                                              · linarith only [h1233, h906, hlam]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1235 | h1235
                                                · linarith only [h1231, h1235, h934, hc36, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1237 | h1237
                                                  · linarith only [h1237, h934, hlam]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1239 | h1239
                                                    · linarith only [h1237, h1239, hc46, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1241 | h1241
                                                      · linarith only [h1241, hc56, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo0]
                                                      · linarith only [h1241, h954, hlam]
                        · linarith only [h970, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo5]
                      · linarith only [h969, hlam, p0_0]
                    · linarith only [h968, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h906, h967, hlam, p0_1]
                · linarith only [h866, h966, hlam, p0_1]
    · linarith only [h865, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1250 | h1250
    · rcases p0_3 (m.d 1 2) (by simp) with h1251 | h1251
      · rcases p0_3 (m.d 1 3) (by simp) with h1252 | h1252
        · rcases p0_3 (m.d 1 4) (by simp) with h1253 | h1253
          · rcases p0_3 (m.d 1 5) (by simp) with h1254 | h1254
            · rcases p0_3 (m.d 1 6) (by simp) with h1255 | h1255
              · linarith only [h1255, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1257 | h1257
                · linarith only [h1251, h1257, hlam]
                · linarith only [h1257, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1260 | h1260
              · linarith only [h1260, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1262 | h1262
                · linarith only [h1251, h1262, hlam]
                · linarith only [h1254, h1262, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h1265 | h1265
            · rcases p0_3 (m.d 1 6) (by simp) with h1266 | h1266
              · linarith only [h1266, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1268 | h1268
                · linarith only [h1251, h1268, hlam]
                · linarith only [h1253, h1268, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1271 | h1271
              · linarith only [h1271, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1273 | h1273
                · linarith only [h1251, h1273, hlam]
                · linarith only [h1253, h1273, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h1276 | h1276
          · rcases p0_3 (m.d 1 5) (by simp) with h1277 | h1277
            · rcases p0_3 (m.d 1 6) (by simp) with h1278 | h1278
              · linarith only [h1278, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1280 | h1280
                · linarith only [h1251, h1280, hlam]
                · linarith only [h1252, h1280, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1283 | h1283
              · linarith only [h1283, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1285 | h1285
                · linarith only [h1251, h1285, hlam]
                · linarith only [h1252, h1285, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h1288 | h1288
            · rcases p0_3 (m.d 1 6) (by simp) with h1289 | h1289
              · linarith only [h1289, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1291 | h1291
                · linarith only [h1251, h1291, hlam]
                · linarith only [h1252, h1291, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1294 | h1294
              · linarith only [h1294, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1296 | h1296
                · linarith only [h1251, h1296, hlam]
                · linarith only [h1252, h1296, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h1299 | h1299
        · rcases p0_3 (m.d 1 4) (by simp) with h1300 | h1300
          · rcases p0_3 (m.d 1 5) (by simp) with h1301 | h1301
            · rcases p0_3 (m.d 1 6) (by simp) with h1302 | h1302
              · linarith only [h1302, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1304 | h1304
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1305 | h1305
                  · linarith only [h1299, h1305, hlam]
                  · linarith only [h1251, h1305, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h1251, h1304, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1309 | h1309
              · linarith only [h1309, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1311 | h1311
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1312 | h1312
                  · linarith only [h1299, h1312, hlam]
                  · linarith only [h1251, h1312, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h1251, h1311, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h1316 | h1316
            · rcases p0_3 (m.d 1 6) (by simp) with h1317 | h1317
              · linarith only [h1317, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1319 | h1319
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1320 | h1320
                  · linarith only [h1299, h1320, hlam]
                  · linarith only [h1251, h1320, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h1251, h1319, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1324 | h1324
              · linarith only [h1324, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1326 | h1326
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1327 | h1327
                  · linarith only [h1299, h1327, hlam]
                  · linarith only [h1251, h1327, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h1251, h1326, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h1331 | h1331
          · rcases p0_3 (m.d 1 5) (by simp) with h1332 | h1332
            · rcases p0_3 (m.d 1 6) (by simp) with h1333 | h1333
              · linarith only [h1333, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1335 | h1335
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1336 | h1336
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1337 | h1337
                    · linarith only [h1331, h1337, hlam]
                    · linarith only [h1251, h1337, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h1299, h1336, hlam, p0_1]
                · linarith only [h1251, h1335, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1342 | h1342
              · linarith only [h1342, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1344 | h1344
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1345 | h1345
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1346 | h1346
                    · linarith only [h1331, h1346, hlam]
                    · linarith only [h1251, h1346, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h1299, h1345, hlam, p0_1]
                · linarith only [h1251, h1344, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h1351 | h1351
            · rcases p0_3 (m.d 1 6) (by simp) with h1352 | h1352
              · linarith only [h1352, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1354 | h1354
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1355 | h1355
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1356 | h1356
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1357 | h1357
                      · linarith only [h1351, h1357, hlam]
                      · linarith only [h1251, h1357, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h1331, h1356, hlam, p0_1]
                  · linarith only [h1299, h1355, hlam, p0_1]
                · linarith only [h1251, h1354, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h1363 | h1363
              · linarith only [h1363, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1365 | h1365
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1366 | h1366
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1367 | h1367
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1368 | h1368
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1369 | h1369
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1370 | h1370
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1371 | h1371
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1372 | h1372
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1373 | h1373
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1374 | h1374
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1375 | h1375
                                    · linarith only [h1251, h1375, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1377 | h1377
                                      · linarith only [h1370, h1375, h1377, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1379 | h1379
                                        · linarith only [h1251, h1379, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1381 | h1381
                                          · linarith only [h1251, h1381, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1383 | h1383
                                            · linarith only [h1299, h1383, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1385 | h1385
                                              · linarith only [h1365, h1370, h1372, h1383, h1385, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1387 | h1387
                                                · linarith only [h1299, h1387, hlam]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1389 | h1389
                                                  · linarith only [h1331, h1389, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1391 | h1391
                                                    · linarith only [h1331, h1391, hlam]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1393 | h1393
                                                      · linarith only [h1351, h1393, hlam]
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1395 | h1395
                                                        · linarith only [h1365, h1370, h1375, h1383, h1395, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                                                        · linarith only [h1365, h1370, h1372, h1375, h1395, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1398 | h1398
                                    · linarith only [h1251, h1398, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1400 | h1400
                                      · linarith only [h1251, h1400, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1402 | h1402
                                        · linarith only [h1365, h1370, h1398, h1402, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1404 | h1404
                                          · linarith only [h1251, h1404, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1406 | h1406
                                            · linarith only [h1299, h1406, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1408 | h1408
                                              · linarith only [h1365, h1370, h1372, h1406, h1408, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1410 | h1410
                                                · linarith only [h1299, h1410, hlam]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1412 | h1412
                                                  · linarith only [h1331, h1374, h1412, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1414 | h1414
                                                    · linarith only [h1331, h1414, hlam]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1416 | h1416
                                                      · linarith only [h1351, h1416, hlam]
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1418 | h1418
                                                        · linarith only [h1365, h1370, h1398, h1406, h1418, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                                                        · linarith only [h1372, h1374, h1398, h1418, hc12, hc45, hlam, hphi, ht23, ht34]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1421 | h1421
                                  · linarith only [h1372, h1373, h1421, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1423 | h1423
                                    · linarith only [h1251, h1423, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1425 | h1425
                                      · linarith only [h1365, h1370, h1423, h1425, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1427 | h1427
                                        · linarith only [h1365, h1370, h1423, h1427, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1429 | h1429
                                          · linarith only [h1251, h1429, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1431 | h1431
                                            · linarith only [h1299, h1431, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h1372, h1373, h1431, hc13, hc35, hlam, hphi]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1434 | h1434
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1435 | h1435
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1436 | h1436
                                    · linarith only [h1251, h1436, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1438 | h1438
                                      · linarith only [h1251, h1438, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1440 | h1440
                                        · linarith only [h1299, h1436, h1440, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1442 | h1442
                                          · linarith only [h1251, h1442, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1444 | h1444
                                            · linarith only [h1299, h1372, h1444, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1446 | h1446
                                              · linarith only [h1331, h1444, h1446, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                              · linarith only [h1372, h1434, h1436, h1446, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h1372, h1434, h1435, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1450 | h1450
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1451 | h1451
                                    · linarith only [h1251, h1451, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1453 | h1453
                                      · linarith only [h1365, h1370, h1451, h1453, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1455 | h1455
                                        · linarith only [h1365, h1370, h1451, h1455, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1457 | h1457
                                          · linarith only [h1251, h1457, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1459 | h1459
                                            · linarith only [h1299, h1372, h1459, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1461 | h1461
                                              · linarith only [h1331, h1434, h1459, h1461, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1463 | h1463
                                                · linarith only [h1299, h1463, hlam]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1465 | h1465
                                                  · linarith only [h1331, h1465, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1467 | h1467
                                                    · linarith only [h1331, h1467, hlam]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1469 | h1469
                                                      · linarith only [h1351, h1469, hlam]
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1471 | h1471
                                                        · linarith only [h1370, h1372, h1450, h1451, h1459, h1465, h1471, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1473 | h1473
                                                          · linarith only [h1365, h1366, h1370, h1434, h1451, h1473, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1475 | h1475
                                                            · linarith only [h1365, h1371, h1451, h1459, h1465, h1475, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                                                            · linarith only [h1450, h1453, h1475, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1478 | h1478
                                    · linarith only [h1251, h1478, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1480 | h1480
                                      · linarith only [h1251, h1480, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1482 | h1482
                                        · linarith only [h1299, h1478, h1482, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1484 | h1484
                                          · linarith only [h1251, h1484, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1486 | h1486
                                            · linarith only [h1299, h1486, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1488 | h1488
                                              · linarith only [h1331, h1434, h1486, h1488, hc05, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1490 | h1490
                                                · linarith only [h1299, h1490, hlam]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1492 | h1492
                                                  · linarith only [h1331, h1450, h1492, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1494 | h1494
                                                    · linarith only [h1331, h1494, hlam]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1496 | h1496
                                                      · linarith only [h1351, h1496, hlam]
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1498 | h1498
                                                        · linarith only [h1370, h1372, h1498, hlam]
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1500 | h1500
                                                          · linarith only [h1370, h1434, h1500, hlam]
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1502 | h1502
                                                            · linarith only [h1365, h1371, h1372, h1450, h1502, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h1504 | h1504
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1505 | h1505
                                                                · linarith only [h1370, h1372, h1450, h1478, h1505, hc12, hc34, hlam, hphi, ht23]
                                                                · linarith only [h1370, h1372, h1478, h1505, hc12, hc45, hlam, hphi, ht23, ht34]
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1508 | h1508
                                                                · linarith only [h1370, h1372, h1450, h1478, h1508, hc12, hc34, hlam, hphi, ht23]
                                                                · linarith only [h1370, h1372, h1478, h1508, hc12, hc45, hlam, hphi, ht23, ht34]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1511 | h1511
                              · linarith only [h1370, h1371, h1511, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1513 | h1513
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1514 | h1514
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1515 | h1515
                                    · linarith only [h1251, h1515, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h1370, h1371, h1515, hc12, hc24, hlam, hphi]
                                  · linarith only [h1370, h1371, h1513, h1514, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1519 | h1519
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1520 | h1520
                                    · linarith only [h1251, h1520, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h1370, h1371, h1520, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1523 | h1523
                                    · linarith only [h1251, h1523, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · linarith only [h1370, h1371, h1519, h1523, hc12, hc45, hlam, hphi, ht23, ht34]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1526 | h1526
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1527 | h1527
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1528 | h1528
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1529 | h1529
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1530 | h1530
                                    · linarith only [h1370, h1526, h1530, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo1]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1532 | h1532
                                      · linarith only [h1299, h1530, h1532, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · linarith only [h1370, h1526, h1532, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1535 | h1535
                                    · linarith only [h1370, h1526, h1535, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo1]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1537 | h1537
                                      · linarith only [h1299, h1535, h1537, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · linarith only [h1370, h1526, h1537, hc12, hc23, hlam, hphi]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1540 | h1540
                                  · linarith only [h1370, h1526, h1528, h1540, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1542 | h1542
                                    · linarith only [h1251, h1542, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1544 | h1544
                                      · linarith only [h1299, h1542, h1544, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · linarith only [h1370, h1526, h1528, h1544, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1370, h1526, h1527, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1548 | h1548
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1549 | h1549
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1550 | h1550
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1551 | h1551
                                    · linarith only [h1251, h1370, h1551, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1553 | h1553
                                      · linarith only [h1365, h1526, h1553, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1555 | h1555
                                        · linarith only [h1251, h1555, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1557 | h1557
                                          · linarith only [h1251, h1557, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1559 | h1559
                                            · linarith only [h1299, h1559, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1561 | h1561
                                              · linarith only [h1366, h1548, h1559, h1561, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1563 | h1563
                                                · linarith only [h1299, h1563, hlam]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1565 | h1565
                                                  · linarith only [h1331, h1565, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1567 | h1567
                                                    · linarith only [h1331, h1567, hlam]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1569 | h1569
                                                      · linarith only [h1351, h1569, hlam]
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1571 | h1571
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1572 | h1572
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1573 | h1573
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h1574 | h1574
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1575 | h1575
                                                                · linarith only [h1366, h1548, h1551, h1559, h1565, h1575, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                                                                · linarith only [h1550, h1551, h1559, h1575, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1578 | h1578
                                                                · linarith only [h1366, h1548, h1551, h1559, h1565, h1578, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                                                                · linarith only [h1550, h1551, h1559, h1578, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                                            · linarith only [h1526, h1550, h1573, hlam]
                                                          · linarith only [h1370, h1548, h1551, h1559, h1572, hc12, hc35, hlam, hphi, ht23]
                                                        · linarith only [h1370, h1548, h1550, h1551, h1559, h1565, h1571, hc12, hc34, hlam, hphi, ht23]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1584 | h1584
                                    · linarith only [h1251, h1370, h1584, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1586 | h1586
                                      · linarith only [h1251, h1526, h1586, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1588 | h1588
                                        · linarith only [h1299, h1584, h1588, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1590 | h1590
                                          · linarith only [h1251, h1590, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1592 | h1592
                                            · linarith only [h1299, h1592, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1594 | h1594
                                              · linarith only [h1366, h1548, h1592, h1594, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1596 | h1596
                                                · linarith only [h1299, h1596, hlam]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1598 | h1598
                                                  · linarith only [h1331, h1598, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1600 | h1600
                                                    · linarith only [h1331, h1600, hlam]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1602 | h1602
                                                      · linarith only [h1351, h1602, hlam]
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1604 | h1604
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1605 | h1605
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1606 | h1606
                                                            · linarith only [h1548, h1550, h1584, h1592, h1606, hc12, hc24, hlam, hphi]
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h1608 | h1608
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1609 | h1609
                                                                · linarith only [h1365, h1526, h1548, h1606, h1609, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h1611 | h1611
                                                                  · linarith only [h1366, h1549, h1592, h1598, h1602, h1611, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                                                                  · linarith only [h1584, h1592, h1608, h1609, h1611, hc12, hc25, hlam, hphi]
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1614 | h1614
                                                                · linarith only [h1366, h1548, h1550, h1614, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h1616 | h1616
                                                                  · linarith only [h1366, h1549, h1606, h1608, h1616, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                                                                  · rcases m.htr 4 5 6 (by decide) (by decide) with h1618 | h1618
                                                                    · linarith only [h1526, h1548, h1584, h1592, h1606, h1608, h1618, hc12, hc45, hlam, hphi, ht23, ht34]
                                                                    · linarith only [h1548, h1550, h1584, h1592, h1618, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                                          · linarith only [h1370, h1548, h1584, h1592, h1605, hc12, hc35, hlam, hphi, ht23]
                                                        · linarith only [h1370, h1548, h1604, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1623 | h1623
                                  · linarith only [h1548, h1549, h1623, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1625 | h1625
                                    · linarith only [h1251, h1370, h1625, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1627 | h1627
                                      · linarith only [h1365, h1526, h1627, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1629 | h1629
                                        · linarith only [h1299, h1625, h1629, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1631 | h1631
                                          · linarith only [h1251, h1631, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1633 | h1633
                                            · linarith only [h1299, h1633, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · linarith only [h1548, h1549, h1625, h1633, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h1636 | h1636
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1637 | h1637
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1638 | h1638
                                    · linarith only [h1251, h1370, h1638, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1640 | h1640
                                      · linarith only [h1365, h1526, h1640, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1642 | h1642
                                        · linarith only [h1299, h1638, h1642, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1644 | h1644
                                          · linarith only [h1251, h1644, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1646 | h1646
                                            · linarith only [h1299, h1548, h1636, h1646, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1648 | h1648
                                              · linarith only [h1331, h1646, h1648, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                              · linarith only [h1548, h1636, h1638, h1648, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h1548, h1636, h1637, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1652 | h1652
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1653 | h1653
                                    · linarith only [h1251, h1370, h1653, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1655 | h1655
                                      · linarith only [h1365, h1526, h1655, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1657 | h1657
                                        · linarith only [h1251, h1657, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1659 | h1659
                                          · linarith only [h1251, h1659, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1661 | h1661
                                            · linarith only [h1299, h1661, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1663 | h1663
                                              · linarith only [h1331, h1370, h1636, h1661, h1663, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1665 | h1665
                                                · linarith only [h1299, h1665, hlam]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1667 | h1667
                                                  · linarith only [h1331, h1667, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1669 | h1669
                                                    · linarith only [h1331, h1669, hlam]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1671 | h1671
                                                      · linarith only [h1351, h1671, hlam]
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1673 | h1673
                                                        · linarith only [h1548, h1652, h1653, h1661, h1667, h1673, hc12, hc23, hlam, hphi]
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1675 | h1675
                                                          · linarith only [h1636, h1652, h1653, h1661, h1667, h1673, h1675, hc12, hc34, hlam, hphi, ht23]
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1677 | h1677
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h1678 | h1678
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1679 | h1679
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h1680 | h1680
                                                                  · rcases m.htr 4 5 6 (by decide) (by decide) with h1681 | h1681
                                                                    · linarith only [h1652, h1653, h1661, h1667, h1671, h1681, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                                                    · linarith only [h1653, h1661, h1667, h1678, h1681, hc12, hc25, hlam, hphi]
                                                                  · linarith only [h1675, h1678, h1680, hlam]
                                                                · linarith only [h1548, h1652, h1679, hlam]
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1686 | h1686
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h1687 | h1687
                                                                  · linarith only [h1657, h1678, h1687, hc12, hc35, hlam, hphi, ht23]
                                                                  · linarith only [h1365, h1370, h1675, h1687, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                                                · linarith only [h1365, h1367, h1370, h1548, h1652, h1686, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                                                            · linarith only [h1526, h1652, h1677, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1692 | h1692
                                    · linarith only [h1365, h1370, h1692, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1694 | h1694
                                      · linarith only [h1251, h1526, h1694, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1696 | h1696
                                        · linarith only [h1299, h1692, h1696, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1698 | h1698
                                          · linarith only [h1251, h1698, hlam]
                                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1700 | h1700
                                            · linarith only [h1299, h1365, h1370, h1548, h1700, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1702 | h1702
                                              · linarith only [h1299, h1702, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                              · rcases m.htr 1 3 6 (by decide) (by decide) with h1704 | h1704
                                                · linarith only [h1299, h1704, hlam]
                                                · rcases m.htr 1 4 5 (by decide) (by decide) with h1706 | h1706
                                                  · linarith only [h1331, h1706, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                                                  · rcases m.htr 1 4 6 (by decide) (by decide) with h1708 | h1708
                                                    · linarith only [h1331, h1708, hlam]
                                                    · rcases m.htr 1 5 6 (by decide) (by decide) with h1710 | h1710
                                                      · linarith only [h1351, h1710, hlam]
                                                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1712 | h1712
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1713 | h1713
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1714 | h1714
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h1715 | h1715
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1716 | h1716
                                                                · linarith only [h1365, h1526, h1652, h1712, h1716, hc12, hc23, hlam, hphi]
                                                                · linarith only [h1365, h1370, h1548, h1714, h1716, hc12, hc24, hlam, hphi]
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1719 | h1719
                                                                · linarith only [h1365, h1370, h1548, h1652, h1712, h1719, hc12, hc23, hlam, hphi]
                                                                · linarith only [h1365, h1370, h1548, h1712, h1714, h1719, hc12, hc23, hlam, hphi]
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h1722 | h1722
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1723 | h1723
                                                                · linarith only [h1365, h1526, h1714, h1723, hc12, hc34, hlam, hphi, ht23]
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h1725 | h1725
                                                                  · linarith only [h1696, h1710, h1713, h1725, hc12, hc23, hlam, hphi]
                                                                  · linarith only [h1365, h1370, h1636, h1722, h1725, hc12, hc25, hlam, hphi]
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1728 | h1728
                                                                · linarith only [h1365, h1370, h1548, h1652, h1712, h1728, hc12, hc23, hlam, hphi]
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h1730 | h1730
                                                                  · linarith only [h1696, h1722, h1730, hc12, hc35, hlam, hphi, ht23]
                                                                  · rcases m.htr 4 5 6 (by decide) (by decide) with h1732 | h1732
                                                                    · linarith only [h1365, h1370, h1548, h1712, h1714, h1722, h1732, hc12, hc45, hlam, hphi, ht23, ht34]
                                                                    · linarith only [h1365, h1370, h1548, h1712, h1714, h1732, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                                          · linarith only [h1365, h1370, h1548, h1712, h1713, hc12, hc35, hlam, hphi, ht23]
                                                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1736 | h1736
                                                          · linarith only [h1365, h1370, h1636, h1712, h1736, hc12, hc34, hlam, hphi, ht23]
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1738 | h1738
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h1739 | h1739
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1740 | h1740
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h1741 | h1741
                                                                  · rcases m.htr 4 5 6 (by decide) (by decide) with h1742 | h1742
                                                                    · linarith only [h1692, h1700, h1706, h1710, h1738, h1742, hc12, hc24, hlam, hphi]
                                                                    · linarith only [h1365, h1370, h1548, h1652, h1739, h1742, hc12, hc25, hlam, hphi]
                                                                  · linarith only [h1736, h1739, h1741, hlam]
                                                                · linarith only [h1365, h1370, h1712, h1740, hc12, hc45, hlam, hphi, ht23, ht34]
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1747 | h1747
                                                                · rcases m.htr 3 5 6 (by decide) (by decide) with h1748 | h1748
                                                                  · linarith only [h1696, h1739, h1748, hc12, hc35, hlam, hphi, ht23]
                                                                  · linarith only [h1365, h1370, h1736, h1748, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                                                · linarith only [h1365, h1370, h1548, h1738, h1747, hc12, hc24, hlam, hphi]
                                                            · rcases m.htr 2 5 6 (by decide) (by decide) with h1752 | h1752
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1753 | h1753
                                                                · linarith only [h1365, h1526, h1738, h1753, hc12, hc34, hlam, hphi, ht23]
                                                                · linarith only [h1365, h1370, h1712, h1753, hc12, hc45, hlam, hphi, ht23, ht34]
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1756 | h1756
                                                                · linarith only [h1365, h1370, h1712, h1738, h1756, hc12, hc34, hlam, hphi, ht23]
                                                                · linarith only [h1365, h1370, h1712, h1756, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h1369, hlam, p0_0]
                      · linarith only [h1368, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo4]
                    · linarith only [h1251, h1367, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h1299, h1366, hlam, p0_1]
                · linarith only [h1251, h1365, hlam, p0_1]
    · linarith only [h1250, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1767 | h1767
    · rcases p0_3 (m.d 1 2) (by simp) with h1768 | h1768
      · rcases p0_3 (m.d 1 3) (by simp) with h1769 | h1769
        · linarith only [h1769, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h1771 | h1771
          · rcases p0_3 (m.d 1 5) (by simp) with h1772 | h1772
            · rcases p0_3 (m.d 1 6) (by simp) with h1773 | h1773
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1774 | h1774
                · linarith only [h1774, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h1767, h1774, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1777 | h1777
                · linarith only [h1777, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1767, h1777, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h1780 | h1780
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1781 | h1781
                · linarith only [h1781, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1767, h1781, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1784 | h1784
                · linarith only [h1784, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1767, h1784, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h1787 | h1787
            · rcases p0_3 (m.d 1 6) (by simp) with h1788 | h1788
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1789 | h1789
                · linarith only [h1789, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1767, h1789, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1792 | h1792
                · linarith only [h1792, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1767, h1792, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h1795 | h1795
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1796 | h1796
                · linarith only [h1796, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1767, h1796, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1799 | h1799
                · linarith only [h1799, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1767, h1799, hlam]
      · linarith only [h1768, hlam, p0_0]
    · linarith only [h1767, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1804 | h1804
    · rcases p0_3 (m.d 1 2) (by simp) with h1805 | h1805
      · rcases p0_3 (m.d 1 3) (by simp) with h1806 | h1806
        · rcases p0_3 (m.d 1 4) (by simp) with h1807 | h1807
          · linarith only [h1807, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1809 | h1809
            · rcases p0_3 (m.d 1 6) (by simp) with h1810 | h1810
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1811 | h1811
                · linarith only [h1811, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1804, h1811, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1814 | h1814
                · linarith only [h1814, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1804, h1814, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h1817 | h1817
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1818 | h1818
                · linarith only [h1818, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1804, h1818, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1821 | h1821
                · linarith only [h1821, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1804, h1821, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h1824 | h1824
          · linarith only [h1824, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1826 | h1826
            · rcases p0_3 (m.d 1 6) (by simp) with h1827 | h1827
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1828 | h1828
                · linarith only [h1806, h1828, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1804, h1828, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1831 | h1831
                · linarith only [h1806, h1831, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1804, h1831, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h1834 | h1834
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1835 | h1835
                · linarith only [h1806, h1835, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1804, h1835, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1838 | h1838
                · linarith only [h1806, h1838, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1804, h1838, hlam]
      · linarith only [h1805, hlam, p0_0]
    · linarith only [h1804, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1843 | h1843
    · rcases p0_3 (m.d 1 2) (by simp) with h1844 | h1844
      · rcases p0_3 (m.d 1 3) (by simp) with h1845 | h1845
        · rcases p0_3 (m.d 1 4) (by simp) with h1846 | h1846
          · rcases p0_3 (m.d 1 5) (by simp) with h1847 | h1847
            · linarith only [h1847, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1849 | h1849
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1850 | h1850
                · linarith only [h1850, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1843, h1850, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1853 | h1853
                · linarith only [h1853, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1843, h1853, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h1856 | h1856
            · linarith only [h1856, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1858 | h1858
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1859 | h1859
                · linarith only [h1846, h1859, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1843, h1859, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1862 | h1862
                · linarith only [h1846, h1862, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1843, h1862, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h1865 | h1865
          · rcases p0_3 (m.d 1 5) (by simp) with h1866 | h1866
            · linarith only [h1866, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1868 | h1868
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1869 | h1869
                · linarith only [h1845, h1869, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1843, h1869, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1872 | h1872
                · linarith only [h1845, h1872, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1843, h1872, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h1875 | h1875
            · linarith only [h1875, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1877 | h1877
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1878 | h1878
                · linarith only [h1845, h1878, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1843, h1878, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1881 | h1881
                · linarith only [h1845, h1881, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1843, h1881, hlam]
      · linarith only [h1844, hlam, p0_0]
    · linarith only [h1843, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1886 | h1886
    · rcases p0_3 (m.d 1 2) (by simp) with h1887 | h1887
      · rcases p0_3 (m.d 1 3) (by simp) with h1888 | h1888
        · rcases p0_3 (m.d 1 4) (by simp) with h1889 | h1889
          · rcases p0_3 (m.d 1 5) (by simp) with h1890 | h1890
            · rcases p0_3 (m.d 1 6) (by simp) with h1891 | h1891
              · linarith only [h1891, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1893 | h1893
                · linarith only [h1893, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                · linarith only [h1886, h1893, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h1896 | h1896
              · linarith only [h1896, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1898 | h1898
                · linarith only [h1890, h1898, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1886, h1898, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h1901 | h1901
            · rcases p0_3 (m.d 1 6) (by simp) with h1902 | h1902
              · linarith only [h1902, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1904 | h1904
                · linarith only [h1889, h1904, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1886, h1904, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h1907 | h1907
              · linarith only [h1907, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1909 | h1909
                · linarith only [h1889, h1909, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1886, h1909, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h1912 | h1912
          · rcases p0_3 (m.d 1 5) (by simp) with h1913 | h1913
            · rcases p0_3 (m.d 1 6) (by simp) with h1914 | h1914
              · linarith only [h1914, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1916 | h1916
                · linarith only [h1888, h1916, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1886, h1916, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h1919 | h1919
              · linarith only [h1919, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1921 | h1921
                · linarith only [h1888, h1921, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1886, h1921, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h1924 | h1924
            · rcases p0_3 (m.d 1 6) (by simp) with h1925 | h1925
              · linarith only [h1925, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1927 | h1927
                · linarith only [h1888, h1927, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1886, h1927, hlam]
            · rcases p0_3 (m.d 1 6) (by simp) with h1930 | h1930
              · linarith only [h1930, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1932 | h1932
                · linarith only [h1888, h1932, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h1886, h1932, hlam]
      · linarith only [h1887, hlam, p0_0]
    · linarith only [h1886, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1938 | h1938
    · rcases p0_3 (m.d 1 2) (by simp) with h1939 | h1939
      · linarith only [h1939, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h1941 | h1941
        · rcases p0_3 (m.d 1 4) (by simp) with h1942 | h1942
          · rcases p0_3 (m.d 1 5) (by simp) with h1943 | h1943
            · rcases p0_3 (m.d 1 6) (by simp) with h1944 | h1944
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1945 | h1945
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1946 | h1946
                  · linarith only [h1946, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1938, h1946, hlam]
                · linarith only [h1945, hc01, hlam, hphi, p0_1, u1elo2]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1950 | h1950
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1951 | h1951
                  · linarith only [h1951, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1938, h1951, hlam]
                · linarith only [h1950, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases p0_3 (m.d 1 6) (by simp) with h1955 | h1955
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1956 | h1956
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1957 | h1957
                  · linarith only [h1957, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1938, h1957, hlam]
                · linarith only [h1956, hc01, hlam, hphi, p0_1, u1elo2]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1961 | h1961
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1962 | h1962
                  · linarith only [h1962, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1938, h1962, hlam]
                · linarith only [h1961, hc01, hlam, hphi, p0_1, u1elo2]
          · rcases p0_3 (m.d 1 5) (by simp) with h1966 | h1966
            · rcases p0_3 (m.d 1 6) (by simp) with h1967 | h1967
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1968 | h1968
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1969 | h1969
                  · linarith only [h1969, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1938, h1969, hlam]
                · linarith only [h1968, hc01, hlam, hphi, p0_1, u1elo2]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1973 | h1973
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1974 | h1974
                  · linarith only [h1974, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1938, h1974, hlam]
                · linarith only [h1973, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases p0_3 (m.d 1 6) (by simp) with h1978 | h1978
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1979 | h1979
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1980 | h1980
                  · linarith only [h1980, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1938, h1980, hlam]
                · linarith only [h1979, hc01, hlam, hphi, p0_1, u1elo2]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1984 | h1984
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1985 | h1985
                  · linarith only [h1985, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1938, h1985, hlam]
                · linarith only [h1984, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h1941, hlam, p0_0]
    · linarith only [h1938, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1992 | h1992
    · rcases p0_3 (m.d 1 2) (by simp) with h1993 | h1993
      · rcases p0_3 (m.d 1 3) (by simp) with h1994 | h1994
        · rcases p0_3 (m.d 1 4) (by simp) with h1995 | h1995
          · linarith only [h1995, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h1997 | h1997
            · rcases p0_3 (m.d 1 6) (by simp) with h1998 | h1998
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1999 | h1999
                · linarith only [h1993, h1999, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h1992, h1999, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2002 | h2002
                · linarith only [h1993, h2002, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h1992, h2002, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2005 | h2005
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2006 | h2006
                · linarith only [h1993, h2006, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h1992, h2006, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2009 | h2009
                · linarith only [h1993, h2009, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h1992, h2009, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
        · linarith only [h1994, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2013 | h2013
        · rcases p0_3 (m.d 1 4) (by simp) with h2014 | h2014
          · linarith only [h2014, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2016 | h2016
            · rcases p0_3 (m.d 1 6) (by simp) with h2017 | h2017
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2018 | h2018
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2019 | h2019
                  · linarith only [h1993, h2019, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1992, h2019, hlam]
                · linarith only [h1993, h2018, hc01, hlam, hphi, p0_1, u1elo2]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2023 | h2023
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2024 | h2024
                  · linarith only [h1993, h2024, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1992, h2024, hlam]
                · linarith only [h1993, h2023, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases p0_3 (m.d 1 6) (by simp) with h2028 | h2028
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2029 | h2029
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2030 | h2030
                  · linarith only [h1993, h2030, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1992, h2030, hlam]
                · linarith only [h1993, h2029, hc01, hlam, hphi, p0_1, u1elo2]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2034 | h2034
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2035 | h2035
                  · linarith only [h1993, h2035, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h1992, h2035, hlam]
                · linarith only [h1993, h2034, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h2013, hlam, p0_0]
    · linarith only [h1992, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2041 | h2041
    · rcases p0_3 (m.d 1 2) (by simp) with h2042 | h2042
      · rcases p0_3 (m.d 1 3) (by simp) with h2043 | h2043
        · rcases p0_3 (m.d 1 4) (by simp) with h2044 | h2044
          · rcases p0_3 (m.d 1 5) (by simp) with h2045 | h2045
            · linarith only [h2045, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2047 | h2047
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2048 | h2048
                · linarith only [h2042, h2048, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2041, h2048, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2051 | h2051
                · linarith only [h2042, h2051, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2041, h2051, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h2054 | h2054
            · linarith only [h2054, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2056 | h2056
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2057 | h2057
                · linarith only [h2042, h2044, h2057, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2041, h2044, h2057, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2060 | h2060
                · linarith only [h2042, h2044, h2060, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2041, h2044, h2060, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
        · linarith only [h2043, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2064 | h2064
        · rcases p0_3 (m.d 1 4) (by simp) with h2065 | h2065
          · rcases p0_3 (m.d 1 5) (by simp) with h2066 | h2066
            · linarith only [h2066, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2068 | h2068
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2069 | h2069
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2070 | h2070
                  · linarith only [h2042, h2070, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2041, h2070, hlam]
                · linarith only [h2042, h2069, hc01, hlam, hphi, p0_1, u1elo2]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2074 | h2074
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2075 | h2075
                  · linarith only [h2042, h2075, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2041, h2075, hlam]
                · linarith only [h2042, h2074, hc01, hlam, hphi, p0_1, u1elo2]
          · rcases p0_3 (m.d 1 5) (by simp) with h2079 | h2079
            · linarith only [h2079, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2081 | h2081
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2082 | h2082
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2083 | h2083
                  · linarith only [h2042, h2083, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2041, h2083, hlam]
                · linarith only [h2042, h2082, hc01, hlam, hphi, p0_1, u1elo2]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2087 | h2087
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2088 | h2088
                  · linarith only [h2042, h2088, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2041, h2088, hlam]
                · linarith only [h2042, h2087, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h2064, hlam, p0_0]
    · linarith only [h2041, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2094 | h2094
    · rcases p0_3 (m.d 1 2) (by simp) with h2095 | h2095
      · rcases p0_3 (m.d 1 3) (by simp) with h2096 | h2096
        · rcases p0_3 (m.d 1 4) (by simp) with h2097 | h2097
          · rcases p0_3 (m.d 1 5) (by simp) with h2098 | h2098
            · rcases p0_3 (m.d 1 6) (by simp) with h2099 | h2099
              · linarith only [h2099, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2101 | h2101
                · linarith only [h2095, h2101, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                · linarith only [h2094, h2101, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2104 | h2104
              · linarith only [h2104, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2106 | h2106
                · linarith only [h2095, h2098, h2106, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2094, h2098, h2106, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h2109 | h2109
            · rcases p0_3 (m.d 1 6) (by simp) with h2110 | h2110
              · linarith only [h2110, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2112 | h2112
                · linarith only [h2095, h2097, h2112, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2094, h2097, h2112, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2115 | h2115
              · linarith only [h2115, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2117 | h2117
                · linarith only [h2095, h2097, h2117, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2094, h2097, h2117, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
        · linarith only [h2096, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2121 | h2121
        · rcases p0_3 (m.d 1 4) (by simp) with h2122 | h2122
          · rcases p0_3 (m.d 1 5) (by simp) with h2123 | h2123
            · rcases p0_3 (m.d 1 6) (by simp) with h2124 | h2124
              · linarith only [h2124, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2126 | h2126
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2127 | h2127
                  · linarith only [h2095, h2127, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2094, h2127, hlam]
                · linarith only [h2095, h2126, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases p0_3 (m.d 1 6) (by simp) with h2131 | h2131
              · linarith only [h2131, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2133 | h2133
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2134 | h2134
                  · linarith only [h2095, h2134, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2094, h2134, hlam]
                · linarith only [h2095, h2133, hc01, hlam, hphi, p0_1, u1elo2]
          · rcases p0_3 (m.d 1 5) (by simp) with h2138 | h2138
            · rcases p0_3 (m.d 1 6) (by simp) with h2139 | h2139
              · linarith only [h2139, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2141 | h2141
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2142 | h2142
                  · linarith only [h2095, h2142, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2094, h2142, hlam]
                · linarith only [h2095, h2141, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases p0_3 (m.d 1 6) (by simp) with h2146 | h2146
              · linarith only [h2146, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2148 | h2148
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2149 | h2149
                  · linarith only [h2095, h2149, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2094, h2149, hlam]
                · linarith only [h2095, h2148, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h2121, hlam, p0_0]
    · linarith only [h2094, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2156 | h2156
    · rcases p0_3 (m.d 1 2) (by simp) with h2157 | h2157
      · linarith only [h2157, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2159 | h2159
        · rcases p0_3 (m.d 1 4) (by simp) with h2160 | h2160
          · rcases p0_3 (m.d 1 5) (by simp) with h2161 | h2161
            · rcases p0_3 (m.d 1 6) (by simp) with h2162 | h2162
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2163 | h2163
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2164 | h2164
                  · linarith only [h2159, h2164, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2156, h2164, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2156, h2163, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2168 | h2168
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2169 | h2169
                  · linarith only [h2159, h2169, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2156, h2169, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2156, h2168, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2173 | h2173
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2174 | h2174
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2175 | h2175
                  · linarith only [h2159, h2175, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2156, h2175, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2156, h2174, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2179 | h2179
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2180 | h2180
                  · linarith only [h2159, h2180, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2156, h2180, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2156, h2179, hlam, p0_1]
          · linarith only [h2160, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2185 | h2185
          · rcases p0_3 (m.d 1 5) (by simp) with h2186 | h2186
            · rcases p0_3 (m.d 1 6) (by simp) with h2187 | h2187
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2188 | h2188
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2189 | h2189
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2190 | h2190
                    · linarith only [h2190, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2156, h2190, hlam]
                  · linarith only [h2159, h2189, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2156, h2188, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2195 | h2195
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2196 | h2196
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2197 | h2197
                    · linarith only [h2197, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2156, h2197, hlam]
                  · linarith only [h2159, h2196, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2156, h2195, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2202 | h2202
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2203 | h2203
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2204 | h2204
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2205 | h2205
                    · linarith only [h2205, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2156, h2205, hlam]
                  · linarith only [h2159, h2204, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2156, h2203, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2210 | h2210
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2211 | h2211
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2212 | h2212
                    · linarith only [h2212, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2156, h2212, hlam]
                  · linarith only [h2159, h2211, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2156, h2210, hlam, p0_1]
          · linarith only [h2185, hlam, p0_0]
    · linarith only [h2156, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2219 | h2219
    · rcases p0_3 (m.d 1 2) (by simp) with h2220 | h2220
      · rcases p0_3 (m.d 1 3) (by simp) with h2221 | h2221
        · linarith only [h2221, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2223 | h2223
          · rcases p0_3 (m.d 1 5) (by simp) with h2224 | h2224
            · rcases p0_3 (m.d 1 6) (by simp) with h2225 | h2225
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2226 | h2226
                · linarith only [h2220, h2226, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2219, h2226, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2229 | h2229
                · linarith only [h2220, h2229, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2219, h2229, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2232 | h2232
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2233 | h2233
                · linarith only [h2220, h2233, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2219, h2233, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2236 | h2236
                · linarith only [h2220, h2236, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2219, h2236, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
          · linarith only [h2223, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2240 | h2240
        · linarith only [h2240, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2242 | h2242
          · rcases p0_3 (m.d 1 5) (by simp) with h2243 | h2243
            · rcases p0_3 (m.d 1 6) (by simp) with h2244 | h2244
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2245 | h2245
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2246 | h2246
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2247 | h2247
                    · linarith only [h2220, h2247, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2219, h2247, hlam]
                  · linarith only [h2246, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2219, h2220, h2245, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2252 | h2252
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2253 | h2253
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2254 | h2254
                    · linarith only [h2220, h2254, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                    · linarith only [h2219, h2254, hlam]
                  · linarith only [h2253, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2219, h2220, h2252, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2259 | h2259
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2260 | h2260
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2261 | h2261
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2262 | h2262
                    · linarith only [h2220, h2262, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2219, h2262, hlam]
                  · linarith only [h2261, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2219, h2260, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2267 | h2267
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2268 | h2268
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2269 | h2269
                    · linarith only [h2220, h2269, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2219, h2269, hlam]
                  · linarith only [h2268, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2219, h2220, h2267, hlam, p0_1]
          · linarith only [h2242, hlam, p0_0]
    · linarith only [h2219, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2277 | h2277
    · rcases p0_3 (m.d 1 2) (by simp) with h2278 | h2278
      · rcases p0_3 (m.d 1 3) (by simp) with h2279 | h2279
        · rcases p0_3 (m.d 1 4) (by simp) with h2280 | h2280
          · rcases p0_3 (m.d 1 5) (by simp) with h2281 | h2281
            · linarith only [h2281, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2283 | h2283
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2284 | h2284
                · linarith only [h2278, h2284, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2277, h2284, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2287 | h2287
                · linarith only [h2278, h2287, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2277, h2287, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
          · linarith only [h2280, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2291 | h2291
          · rcases p0_3 (m.d 1 5) (by simp) with h2292 | h2292
            · linarith only [h2292, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2294 | h2294
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2295 | h2295
                · linarith only [h2278, h2279, h2295, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2277, h2279, h2295, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2298 | h2298
                · linarith only [h2278, h2279, h2298, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2277, h2279, h2298, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
          · linarith only [h2291, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2302 | h2302
        · rcases p0_3 (m.d 1 4) (by simp) with h2303 | h2303
          · rcases p0_3 (m.d 1 5) (by simp) with h2304 | h2304
            · linarith only [h2304, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2306 | h2306
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2307 | h2307
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2308 | h2308
                  · linarith only [h2278, h2302, h2308, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2277, h2278, h2308, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2277, h2278, h2307, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2312 | h2312
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2313 | h2313
                  · linarith only [h2278, h2302, h2313, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2277, h2278, h2313, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2277, h2278, h2312, hlam, p0_1]
          · linarith only [h2303, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2318 | h2318
          · rcases p0_3 (m.d 1 5) (by simp) with h2319 | h2319
            · linarith only [h2319, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2321 | h2321
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2322 | h2322
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2323 | h2323
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2324 | h2324
                    · linarith only [h2278, h2324, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2277, h2324, hlam]
                  · linarith only [h2302, h2323, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2277, h2278, h2322, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2329 | h2329
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2330 | h2330
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2331 | h2331
                    · linarith only [h2278, h2331, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2277, h2331, hlam]
                  · linarith only [h2302, h2330, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2277, h2302, h2329, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
          · linarith only [h2318, hlam, p0_0]
    · linarith only [h2277, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2338 | h2338
    · rcases p0_3 (m.d 1 2) (by simp) with h2339 | h2339
      · rcases p0_3 (m.d 1 3) (by simp) with h2340 | h2340
        · rcases p0_3 (m.d 1 4) (by simp) with h2341 | h2341
          · rcases p0_3 (m.d 1 5) (by simp) with h2342 | h2342
            · rcases p0_3 (m.d 1 6) (by simp) with h2343 | h2343
              · linarith only [h2343, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2345 | h2345
                · linarith only [h2339, h2345, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                · linarith only [h2338, h2345, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2348 | h2348
              · linarith only [h2348, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2350 | h2350
                · linarith only [h2339, h2342, h2350, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2338, h2342, h2350, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
          · linarith only [h2341, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2354 | h2354
          · rcases p0_3 (m.d 1 5) (by simp) with h2355 | h2355
            · rcases p0_3 (m.d 1 6) (by simp) with h2356 | h2356
              · linarith only [h2356, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2358 | h2358
                · linarith only [h2339, h2340, h2358, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2338, h2340, h2358, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2361 | h2361
              · linarith only [h2361, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2363 | h2363
                · linarith only [h2339, h2340, h2363, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2338, h2340, h2363, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
          · linarith only [h2354, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2367 | h2367
        · rcases p0_3 (m.d 1 4) (by simp) with h2368 | h2368
          · rcases p0_3 (m.d 1 5) (by simp) with h2369 | h2369
            · rcases p0_3 (m.d 1 6) (by simp) with h2370 | h2370
              · linarith only [h2370, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2372 | h2372
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2373 | h2373
                  · linarith only [h2339, h2367, h2373, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2338, h2339, h2373, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2338, h2339, h2372, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2377 | h2377
              · linarith only [h2377, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2379 | h2379
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2380 | h2380
                  · linarith only [h2339, h2367, h2380, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2338, h2339, h2380, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2338, h2339, h2379, hlam, p0_1]
          · linarith only [h2368, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2385 | h2385
          · rcases p0_3 (m.d 1 5) (by simp) with h2386 | h2386
            · rcases p0_3 (m.d 1 6) (by simp) with h2387 | h2387
              · linarith only [h2387, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2389 | h2389
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2390 | h2390
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2391 | h2391
                    · linarith only [h2339, h2391, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2338, h2391, hlam]
                  · linarith only [h2367, h2390, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2338, h2339, h2389, hlam, p0_1]
            · rcases p0_3 (m.d 1 6) (by simp) with h2396 | h2396
              · linarith only [h2396, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2398 | h2398
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2399 | h2399
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2400 | h2400
                    · linarith only [h2339, h2400, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2338, h2400, hlam]
                  · linarith only [h2367, h2399, hc01, hlam, hphi, p0_1, u1elo3]
                · linarith only [h2338, h2367, h2398, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
          · linarith only [h2385, hlam, p0_0]
    · linarith only [h2338, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2408 | h2408
    · rcases p0_3 (m.d 1 2) (by simp) with h2409 | h2409
      · linarith only [h2409, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2411 | h2411
        · rcases p0_3 (m.d 1 4) (by simp) with h2412 | h2412
          · rcases p0_3 (m.d 1 5) (by simp) with h2413 | h2413
            · rcases p0_3 (m.d 1 6) (by simp) with h2414 | h2414
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2415 | h2415
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2416 | h2416
                  · linarith only [h2411, h2416, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2408, h2416, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2408, h2415, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2420 | h2420
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2421 | h2421
                  · linarith only [h2411, h2421, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2408, h2421, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2408, h2420, hlam, p0_1]
            · linarith only [h2413, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2426 | h2426
            · rcases p0_3 (m.d 1 6) (by simp) with h2427 | h2427
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2428 | h2428
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2429 | h2429
                  · linarith only [h2411, h2429, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2408, h2429, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2408, h2428, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2433 | h2433
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2434 | h2434
                  · linarith only [h2411, h2434, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2408, h2434, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2408, h2433, hlam, p0_1]
            · linarith only [h2426, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2439 | h2439
          · rcases p0_3 (m.d 1 5) (by simp) with h2440 | h2440
            · rcases p0_3 (m.d 1 6) (by simp) with h2441 | h2441
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2442 | h2442
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2443 | h2443
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2444 | h2444
                    · linarith only [h2439, h2444, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2408, h2444, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2408, h2411, h2443, hlam, p0_1]
                · linarith only [h2408, h2442, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2449 | h2449
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2450 | h2450
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2451 | h2451
                    · linarith only [h2439, h2451, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2408, h2451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2408, h2411, h2450, hlam, p0_1]
                · linarith only [h2408, h2449, hlam, p0_1]
            · linarith only [h2440, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2457 | h2457
            · rcases p0_3 (m.d 1 6) (by simp) with h2458 | h2458
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2459 | h2459
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2460 | h2460
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2461 | h2461
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2462 | h2462
                      · linarith only [h2462, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2408, h2462, hlam]
                    · linarith only [h2439, h2461, hc01, hlam, hphi, p0_1, u1elo4]
                  · linarith only [h2408, h2411, h2460, hlam, p0_1]
                · linarith only [h2408, h2459, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2468 | h2468
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2469 | h2469
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2470 | h2470
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2471 | h2471
                      · linarith only [h2471, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2408, h2471, hlam]
                    · linarith only [h2439, h2470, hc01, hlam, hphi, p0_1, u1elo4]
                  · linarith only [h2408, h2411, h2469, hlam, p0_1]
                · linarith only [h2408, h2468, hlam, p0_1]
            · linarith only [h2457, hlam, p0_0]
    · linarith only [h2408, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2479 | h2479
    · rcases p0_3 (m.d 1 2) (by simp) with h2480 | h2480
      · rcases p0_3 (m.d 1 3) (by simp) with h2481 | h2481
        · linarith only [h2481, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2483 | h2483
          · rcases p0_3 (m.d 1 5) (by simp) with h2484 | h2484
            · rcases p0_3 (m.d 1 6) (by simp) with h2485 | h2485
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2486 | h2486
                · linarith only [h2480, h2486, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h2479, h2486, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2489 | h2489
                · linarith only [h2480, h2489, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2479, h2489, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · linarith only [h2484, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2493 | h2493
            · rcases p0_3 (m.d 1 6) (by simp) with h2494 | h2494
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2495 | h2495
                · linarith only [h2480, h2495, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2479, h2495, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2498 | h2498
                · linarith only [h2480, h2498, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2479, h2498, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · linarith only [h2493, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2502 | h2502
        · linarith only [h2502, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2504 | h2504
          · rcases p0_3 (m.d 1 5) (by simp) with h2505 | h2505
            · rcases p0_3 (m.d 1 6) (by simp) with h2506 | h2506
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2507 | h2507
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2508 | h2508
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2509 | h2509
                    · linarith only [h2480, h2504, h2509, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2479, h2480, h2509, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2479, h2508, hlam, p0_1]
                · linarith only [h2479, h2480, h2507, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2514 | h2514
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2515 | h2515
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2516 | h2516
                    · linarith only [h2480, h2504, h2516, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2479, h2480, h2516, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2479, h2515, hlam, p0_1]
                · linarith only [h2479, h2480, h2514, hlam, p0_1]
            · linarith only [h2505, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2522 | h2522
            · rcases p0_3 (m.d 1 6) (by simp) with h2523 | h2523
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2524 | h2524
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2525 | h2525
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2526 | h2526
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2527 | h2527
                      · linarith only [h2480, h2527, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2479, h2527, hlam]
                    · linarith only [h2504, h2526, hc01, hlam, hphi, p0_1, u1elo4]
                  · linarith only [h2479, h2525, hlam, p0_1]
                · linarith only [h2479, h2480, h2524, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2533 | h2533
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2534 | h2534
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2535 | h2535
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2536 | h2536
                      · linarith only [h2480, h2536, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2479, h2536, hlam]
                    · linarith only [h2504, h2535, hc01, hlam, hphi, p0_1, u1elo4]
                  · linarith only [h2479, h2534, hlam, p0_1]
                · linarith only [h2479, h2480, h2533, hlam, p0_1]
            · linarith only [h2522, hlam, p0_0]
    · linarith only [h2479, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2544 | h2544
    · rcases p0_3 (m.d 1 2) (by simp) with h2545 | h2545
      · rcases p0_3 (m.d 1 3) (by simp) with h2546 | h2546
        · rcases p0_3 (m.d 1 4) (by simp) with h2547 | h2547
          · linarith only [h2547, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2549 | h2549
            · rcases p0_3 (m.d 1 6) (by simp) with h2550 | h2550
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2551 | h2551
                · linarith only [h2545, h2551, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h2544, h2551, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2554 | h2554
                · linarith only [h2545, h2554, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2544, h2554, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
            · linarith only [h2549, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2558 | h2558
          · linarith only [h2558, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2560 | h2560
            · rcases p0_3 (m.d 1 6) (by simp) with h2561 | h2561
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2562 | h2562
                · linarith only [h2545, h2546, h2562, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2544, h2546, h2562, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2565 | h2565
                · linarith only [h2545, h2546, h2565, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2544, h2546, h2565, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · linarith only [h2560, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2569 | h2569
        · rcases p0_3 (m.d 1 4) (by simp) with h2570 | h2570
          · linarith only [h2570, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2572 | h2572
            · rcases p0_3 (m.d 1 6) (by simp) with h2573 | h2573
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2574 | h2574
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2575 | h2575
                  · linarith only [h2545, h2569, h2575, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2544, h2545, h2575, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2544, h2545, h2574, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2579 | h2579
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2580 | h2580
                  · linarith only [h2545, h2569, h2580, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2544, h2545, h2580, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2544, h2545, h2579, hlam, p0_1]
            · linarith only [h2572, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2585 | h2585
          · linarith only [h2585, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2587 | h2587
            · rcases p0_3 (m.d 1 6) (by simp) with h2588 | h2588
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2589 | h2589
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2590 | h2590
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2591 | h2591
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2592 | h2592
                      · linarith only [h2545, h2592, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2544, h2592, hlam]
                    · linarith only [h2591, hc01, hlam, hphi, p0_1, u1elo4]
                  · linarith only [h2544, h2569, h2590, hlam, p0_1]
                · linarith only [h2544, h2545, h2589, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2598 | h2598
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2599 | h2599
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2600 | h2600
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2601 | h2601
                      · linarith only [h2545, h2601, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2544, h2601, hlam]
                    · linarith only [h2600, hc01, hlam, hphi, p0_1, u1elo4]
                  · linarith only [h2544, h2569, h2599, hlam, p0_1]
                · linarith only [h2544, h2545, h2598, hlam, p0_1]
            · linarith only [h2587, hlam, p0_0]
    · linarith only [h2544, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2610 | h2610
    · rcases p0_3 (m.d 1 2) (by simp) with h2611 | h2611
      · rcases p0_3 (m.d 1 3) (by simp) with h2612 | h2612
        · rcases p0_3 (m.d 1 4) (by simp) with h2613 | h2613
          · rcases p0_3 (m.d 1 5) (by simp) with h2614 | h2614
            · rcases p0_3 (m.d 1 6) (by simp) with h2615 | h2615
              · linarith only [h2615, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2617 | h2617
                · linarith only [h2611, h2617, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                · linarith only [h2610, h2617, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1, u1elo1]
            · linarith only [h2614, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2621 | h2621
            · rcases p0_3 (m.d 1 6) (by simp) with h2622 | h2622
              · linarith only [h2622, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2624 | h2624
                · linarith only [h2611, h2613, h2624, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2610, h2613, h2624, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
            · linarith only [h2621, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2628 | h2628
          · rcases p0_3 (m.d 1 5) (by simp) with h2629 | h2629
            · rcases p0_3 (m.d 1 6) (by simp) with h2630 | h2630
              · linarith only [h2630, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2632 | h2632
                · linarith only [h2611, h2612, h2632, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2610, h2612, h2632, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · linarith only [h2629, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2636 | h2636
            · rcases p0_3 (m.d 1 6) (by simp) with h2637 | h2637
              · linarith only [h2637, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2639 | h2639
                · linarith only [h2611, h2612, h2639, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2610, h2612, h2639, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
            · linarith only [h2636, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2643 | h2643
        · rcases p0_3 (m.d 1 4) (by simp) with h2644 | h2644
          · rcases p0_3 (m.d 1 5) (by simp) with h2645 | h2645
            · rcases p0_3 (m.d 1 6) (by simp) with h2646 | h2646
              · linarith only [h2646, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2648 | h2648
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2649 | h2649
                  · linarith only [h2611, h2643, h2649, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2610, h2611, h2649, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2610, h2611, h2648, hlam, p0_1]
            · linarith only [h2645, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2654 | h2654
            · rcases p0_3 (m.d 1 6) (by simp) with h2655 | h2655
              · linarith only [h2655, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2657 | h2657
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2658 | h2658
                  · linarith only [h2611, h2643, h2658, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2610, h2611, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2610, h2611, h2657, hlam, p0_1]
            · linarith only [h2654, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2663 | h2663
          · rcases p0_3 (m.d 1 5) (by simp) with h2664 | h2664
            · rcases p0_3 (m.d 1 6) (by simp) with h2665 | h2665
              · linarith only [h2665, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2667 | h2667
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2668 | h2668
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2669 | h2669
                    · linarith only [h2611, h2663, h2669, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2610, h2611, h2669, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2610, h2643, h2668, hlam, p0_1]
                · linarith only [h2610, h2611, h2667, hlam, p0_1]
            · linarith only [h2664, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2675 | h2675
            · rcases p0_3 (m.d 1 6) (by simp) with h2676 | h2676
              · linarith only [h2676, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2678 | h2678
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2679 | h2679
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2680 | h2680
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2681 | h2681
                      · linarith only [h2611, h2681, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2610, h2681, hlam]
                    · linarith only [h2663, h2680, hc01, hlam, hphi, p0_1, u1elo4]
                  · linarith only [h2610, h2643, h2679, hlam, p0_1]
                · linarith only [h2610, h2611, h2678, hlam, p0_1]
            · linarith only [h2675, hlam, p0_0]
    · linarith only [h2610, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2690 | h2690
    · rcases p0_3 (m.d 1 2) (by simp) with h2691 | h2691
      · linarith only [h2691, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2693 | h2693
        · rcases p0_3 (m.d 1 4) (by simp) with h2694 | h2694
          · rcases p0_3 (m.d 1 5) (by simp) with h2695 | h2695
            · rcases p0_3 (m.d 1 6) (by simp) with h2696 | h2696
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2697 | h2697
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2698 | h2698
                  · linarith only [h2693, h2698, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2690, h2698, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2690, h2697, hlam, p0_1]
              · linarith only [h2696, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2703 | h2703
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2704 | h2704
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2705 | h2705
                  · linarith only [h2693, h2705, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2690, h2705, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2690, h2704, hlam, p0_1]
              · linarith only [h2703, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2710 | h2710
            · rcases p0_3 (m.d 1 6) (by simp) with h2711 | h2711
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2712 | h2712
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2713 | h2713
                  · linarith only [h2693, h2713, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2690, h2713, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2690, h2712, hlam, p0_1]
              · linarith only [h2711, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2718 | h2718
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2719 | h2719
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2720 | h2720
                  · linarith only [h2693, h2720, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2690, h2720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2690, h2719, hlam, p0_1]
              · linarith only [h2718, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2725 | h2725
          · rcases p0_3 (m.d 1 5) (by simp) with h2726 | h2726
            · rcases p0_3 (m.d 1 6) (by simp) with h2727 | h2727
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2728 | h2728
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2729 | h2729
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2730 | h2730
                    · linarith only [h2725, h2730, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2690, h2730, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2690, h2693, h2729, hlam, p0_1]
                · linarith only [h2690, h2728, hlam, p0_1]
              · linarith only [h2727, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2736 | h2736
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2737 | h2737
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2738 | h2738
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2739 | h2739
                    · linarith only [h2725, h2739, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2690, h2739, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2690, h2693, h2738, hlam, p0_1]
                · linarith only [h2690, h2737, hlam, p0_1]
              · linarith only [h2736, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2745 | h2745
            · rcases p0_3 (m.d 1 6) (by simp) with h2746 | h2746
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2747 | h2747
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2748 | h2748
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2749 | h2749
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2750 | h2750
                      · linarith only [h2745, h2750, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2690, h2750, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h2690, h2725, h2749, hlam, p0_1]
                  · linarith only [h2690, h2693, h2748, hlam, p0_1]
                · linarith only [h2690, h2747, hlam, p0_1]
              · linarith only [h2746, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2757 | h2757
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2758 | h2758
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2759 | h2759
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2760 | h2760
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2761 | h2761
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2762 | h2762
                        · linarith only [h2762, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                        · linarith only [h2690, h2762, hlam]
                      · linarith only [h2745, h2761, hc01, hlam, hphi, p0_1, u1elo5]
                    · linarith only [h2690, h2725, h2760, hlam, p0_1]
                  · linarith only [h2690, h2693, h2759, hlam, p0_1]
                · linarith only [h2690, h2758, hlam, p0_1]
              · linarith only [h2757, hlam, p0_0]
    · linarith only [h2690, hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2771 | h2771
    · rcases p0_3 (m.d 1 2) (by simp) with h2772 | h2772
      · rcases p0_3 (m.d 1 3) (by simp) with h2773 | h2773
        · linarith only [h2773, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2775 | h2775
          · rcases p0_3 (m.d 1 5) (by simp) with h2776 | h2776
            · rcases p0_3 (m.d 1 6) (by simp) with h2777 | h2777
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2778 | h2778
                · linarith only [h2772, h2778, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h2771, h2778, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2777, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2782 | h2782
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2783 | h2783
                · linarith only [h2772, h2783, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2771, h2783, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2782, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2787 | h2787
            · rcases p0_3 (m.d 1 6) (by simp) with h2788 | h2788
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2789 | h2789
                · linarith only [h2772, h2789, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2771, h2789, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2788, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2793 | h2793
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2794 | h2794
                · linarith only [h2772, h2794, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2771, h2794, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2793, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2798 | h2798
        · linarith only [h2798, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2800 | h2800
          · rcases p0_3 (m.d 1 5) (by simp) with h2801 | h2801
            · rcases p0_3 (m.d 1 6) (by simp) with h2802 | h2802
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2803 | h2803
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2804 | h2804
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2805 | h2805
                    · linarith only [h2772, h2800, h2805, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2771, h2772, h2805, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2771, h2804, hlam, p0_1]
                · linarith only [h2771, h2772, h2803, hlam, p0_1]
              · linarith only [h2802, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2811 | h2811
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2812 | h2812
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2813 | h2813
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2814 | h2814
                    · linarith only [h2772, h2800, h2814, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2771, h2772, h2814, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2771, h2813, hlam, p0_1]
                · linarith only [h2771, h2772, h2812, hlam, p0_1]
              · linarith only [h2811, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2820 | h2820
            · rcases p0_3 (m.d 1 6) (by simp) with h2821 | h2821
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2822 | h2822
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2823 | h2823
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2824 | h2824
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2825 | h2825
                      · linarith only [h2772, h2820, h2825, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2771, h2772, h2825, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h2771, h2800, h2824, hlam, p0_1]
                  · linarith only [h2771, h2823, hlam, p0_1]
                · linarith only [h2771, h2772, h2822, hlam, p0_1]
              · linarith only [h2821, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2832 | h2832
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2833 | h2833
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2834 | h2834
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2835 | h2835
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2836 | h2836
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2837 | h2837
                        · linarith only [h2772, h2837, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                        · linarith only [h2771, h2837, hlam]
                      · linarith only [h2820, h2836, hc01, hlam, hphi, p0_1, u1elo5]
                    · linarith only [h2771, h2800, h2835, hlam, p0_1]
                  · linarith only [h2771, h2834, hlam, p0_1]
                · linarith only [h2771, h2772, h2833, hlam, p0_1]
              · linarith only [h2832, hlam, p0_0]
    · linarith only [h2771, hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2846 | h2846
    · rcases p0_3 (m.d 1 2) (by simp) with h2847 | h2847
      · rcases p0_3 (m.d 1 3) (by simp) with h2848 | h2848
        · rcases p0_3 (m.d 1 4) (by simp) with h2849 | h2849
          · linarith only [h2849, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2851 | h2851
            · rcases p0_3 (m.d 1 6) (by simp) with h2852 | h2852
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2853 | h2853
                · linarith only [h2847, h2853, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo0]
                · linarith only [h2846, h2853, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2852, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2857 | h2857
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2858 | h2858
                · linarith only [h2847, h2858, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2846, h2858, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2857, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2862 | h2862
          · linarith only [h2862, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2864 | h2864
            · rcases p0_3 (m.d 1 6) (by simp) with h2865 | h2865
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2866 | h2866
                · linarith only [h2847, h2848, h2866, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2846, h2848, h2866, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2865, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2870 | h2870
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2871 | h2871
                · linarith only [h2847, h2848, h2871, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2846, h2848, h2871, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2870, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2875 | h2875
        · rcases p0_3 (m.d 1 4) (by simp) with h2876 | h2876
          · linarith only [h2876, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2878 | h2878
            · rcases p0_3 (m.d 1 6) (by simp) with h2879 | h2879
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2880 | h2880
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2881 | h2881
                  · linarith only [h2847, h2875, h2881, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2846, h2847, h2881, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2846, h2847, h2880, hlam, p0_1]
              · linarith only [h2879, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2886 | h2886
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2887 | h2887
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2888 | h2888
                  · linarith only [h2847, h2875, h2888, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2846, h2847, h2888, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2846, h2847, h2887, hlam, p0_1]
              · linarith only [h2886, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2893 | h2893
          · linarith only [h2893, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2895 | h2895
            · rcases p0_3 (m.d 1 6) (by simp) with h2896 | h2896
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2897 | h2897
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2898 | h2898
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2899 | h2899
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2900 | h2900
                      · linarith only [h2847, h2895, h2900, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                      · linarith only [h2846, h2847, h2900, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo4]
                    · linarith only [h2846, h2899, hlam, p0_1]
                  · linarith only [h2846, h2875, h2898, hlam, p0_1]
                · linarith only [h2846, h2847, h2897, hlam, p0_1]
              · linarith only [h2896, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2907 | h2907
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2908 | h2908
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2909 | h2909
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2910 | h2910
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2911 | h2911
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2912 | h2912
                        · linarith only [h2847, h2912, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                        · linarith only [h2846, h2912, hlam]
                      · linarith only [h2895, h2911, hc01, hlam, hphi, p0_1, u1elo5]
                    · linarith only [h2846, h2910, hlam, p0_1]
                  · linarith only [h2846, h2875, h2909, hlam, p0_1]
                · linarith only [h2846, h2847, h2908, hlam, p0_1]
              · linarith only [h2907, hlam, p0_0]
    · linarith only [h2846, hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2921 | h2921
    · rcases p0_3 (m.d 1 2) (by simp) with h2922 | h2922
      · rcases p0_3 (m.d 1 3) (by simp) with h2923 | h2923
        · rcases p0_3 (m.d 1 4) (by simp) with h2924 | h2924
          · rcases p0_3 (m.d 1 5) (by simp) with h2925 | h2925
            · linarith only [h2925, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2927 | h2927
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2928 | h2928
                · linarith only [h2922, h2928, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2921, h2928, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2927, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2932 | h2932
            · linarith only [h2932, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2934 | h2934
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2935 | h2935
                · linarith only [h2922, h2924, h2935, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2921, h2924, h2935, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2934, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2939 | h2939
          · rcases p0_3 (m.d 1 5) (by simp) with h2940 | h2940
            · linarith only [h2940, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2942 | h2942
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2943 | h2943
                · linarith only [h2922, h2923, h2943, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2921, h2923, h2943, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2942, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2947 | h2947
            · linarith only [h2947, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2949 | h2949
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2950 | h2950
                · linarith only [h2922, h2923, h2950, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                · linarith only [h2921, h2923, h2950, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1, u1elo1]
              · linarith only [h2949, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h2954 | h2954
        · rcases p0_3 (m.d 1 4) (by simp) with h2955 | h2955
          · rcases p0_3 (m.d 1 5) (by simp) with h2956 | h2956
            · linarith only [h2956, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2958 | h2958
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2959 | h2959
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2960 | h2960
                  · linarith only [h2922, h2954, h2960, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2921, h2922, h2960, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2921, h2922, h2959, hlam, p0_1]
              · linarith only [h2958, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2965 | h2965
            · linarith only [h2965, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2967 | h2967
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2968 | h2968
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2969 | h2969
                  · linarith only [h2922, h2954, h2969, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                  · linarith only [h2921, h2922, h2969, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo2]
                · linarith only [h2921, h2922, h2968, hlam, p0_1]
              · linarith only [h2967, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h2974 | h2974
          · rcases p0_3 (m.d 1 5) (by simp) with h2975 | h2975
            · linarith only [h2975, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2977 | h2977
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2978 | h2978
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2979 | h2979
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2980 | h2980
                    · linarith only [h2922, h2974, h2980, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                    · linarith only [h2921, h2922, h2980, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u1elo3]
                  · linarith only [h2921, h2954, h2979, hlam, p0_1]
                · linarith only [h2921, h2922, h2978, hlam, p0_1]
              · linarith only [h2977, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h2986 | h2986
            · linarith only [h2986, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h2988 | h2988
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2989 | h2989
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2990 | h2990
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2991 | h2991
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2992 | h2992
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2993 | h2993
                        · linarith only [h2922, h2993, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
                        · linarith only [h2921, h2993, hlam]
                      · linarith only [h2992, hc01, hlam, hphi, p0_1, u1elo5]
                    · linarith only [h2921, h2974, h2991, hlam, p0_1]
                  · linarith only [h2921, h2954, h2990, hlam, p0_1]
                · linarith only [h2921, h2922, h2989, hlam, p0_1]
              · linarith only [h2988, hlam, p0_0]
    · linarith only [h2921, hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

end R2N4
