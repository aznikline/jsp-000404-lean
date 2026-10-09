import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6694000 in
theorem n8l_sBT8_H_I_H_L (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
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
  have hc06 := m.hcor 0 6 (by decide)
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
  have h0bigk := hb0.1
  have h6elo := hb6.1
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 0 6) (by simp) with h8 | h8
              · linarith only [h8, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h10 | h10
                · rcases m.htr 0 1 3 (by decide) (by decide) with h11 | h11
                  · linarith only [h11, h5, hlam]
                  · linarith only [h10, h11, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h10, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h15 | h15
              · linarith only [h15, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h17 | h17
                · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
                  · linarith only [h18, h5, hlam]
                  · linarith only [h17, h18, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h17, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 0 6) (by simp) with h23 | h23
              · linarith only [h23, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
                  · linarith only [h26, h5, hlam]
                  · linarith only [h25, h26, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h25, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h30 | h30
              · linarith only [h30, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
                · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                  · linarith only [h33, h5, hlam]
                  · linarith only [h32, h33, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h37 | h37
          · rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
            · rcases p0_3 (m.d 0 6) (by simp) with h39 | h39
              · linarith only [h39, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h41 | h41
                · rcases m.htr 0 1 3 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h43 | h43
                    · linarith only [h37, h43, hlam]
                    · linarith only [h41, h43, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h41, h42, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h41, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h48 | h48
              · linarith only [h48, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h50 | h50
                · rcases m.htr 0 1 3 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h52 | h52
                    · linarith only [h37, h52, hlam]
                    · linarith only [h50, h52, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h50, h51, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h57 | h57
            · rcases p0_3 (m.d 0 6) (by simp) with h58 | h58
              · linarith only [h58, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h60 | h60
                · rcases m.htr 0 1 3 (by decide) (by decide) with h61 | h61
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h62 | h62
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h63 | h63
                      · linarith only [h57, h63, hlam]
                      · linarith only [h60, h63, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h60, h62, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h60, h61, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h60, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h69 | h69
              · linarith only [h69, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
                · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h75 | h75
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h76 | h76
                          · linarith only [h76, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h5, h76, hlam]
                        · linarith only [h75, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h71, h74, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h71, h73, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h71, h72, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h71, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h85 | h85
    · rcases p0_3 (m.d 0 2) (by simp) with h86 | h86
      · rcases p0_3 (m.d 0 3) (by simp) with h87 | h87
        · linarith only [h87, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h89 | h89
          · rcases p0_3 (m.d 0 5) (by simp) with h90 | h90
            · rcases p0_3 (m.d 0 6) (by simp) with h91 | h91
              · linarith only [h91, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h93 | h93
                · linarith only [h86, h93, hlam]
                · linarith only [h93, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h96 | h96
              · linarith only [h96, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h98 | h98
                · linarith only [h86, h98, hlam]
                · linarith only [h98, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h101 | h101
            · rcases p0_3 (m.d 0 6) (by simp) with h102 | h102
              · linarith only [h102, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h86, hlam]
                · linarith only [h104, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h107 | h107
              · linarith only [h107, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h109 | h109
                · linarith only [h109, h86, hlam]
                · linarith only [h109, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h112 | h112
        · linarith only [h112, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
          · rcases p0_3 (m.d 0 5) (by simp) with h115 | h115
            · rcases p0_3 (m.d 0 6) (by simp) with h116 | h116
              · linarith only [h116, h86, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
                · rcases m.htr 0 1 3 (by decide) (by decide) with h119 | h119
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h120 | h120
                    · linarith only [h114, h120, hlam]
                    · linarith only [h118, h120, h86, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h119, hlam, p0_0]
                · linarith only [h118, h86, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h125 | h125
              · linarith only [h125, h86, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h127 | h127
                · rcases m.htr 0 1 3 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h129 | h129
                    · linarith only [h114, h129, hlam]
                    · linarith only [h127, h129, h86, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h128, hlam, p0_0]
                · linarith only [h127, h86, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · rcases p0_3 (m.d 0 6) (by simp) with h135 | h135
              · linarith only [h135, h86, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h137 | h137
                · rcases m.htr 0 1 3 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h140 | h140
                      · linarith only [h134, h140, hlam]
                      · linarith only [h137, h140, h86, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h137, h139, h86, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h138, hlam, p0_0]
                · linarith only [h137, h86, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h146 | h146
              · linarith only [h146, h86, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h148 | h148
                · rcases m.htr 0 1 3 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h151 | h151
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h152 | h152
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h153 | h153
                          · linarith only [h153, h86, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h155 | h155
                            · linarith only [h153, h155, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h157 | h157
                              · linarith only [h153, h157, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h159 | h159
                                · linarith only [h153, h159, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h159, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                        · linarith only [h152, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h148, h151, h86, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h148, h150, h86, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h149, hlam, p0_0]
                · linarith only [h148, h86, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h85, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h168 | h168
    · rcases p0_3 (m.d 0 2) (by simp) with h169 | h169
      · rcases p0_3 (m.d 0 3) (by simp) with h170 | h170
        · rcases p0_3 (m.d 0 4) (by simp) with h171 | h171
          · linarith only [h171, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h173 | h173
            · rcases p0_3 (m.d 0 6) (by simp) with h174 | h174
              · linarith only [h174, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h176 | h176
                · linarith only [h169, h176, hlam]
                · linarith only [h176, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h179 | h179
              · linarith only [h179, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h181 | h181
                · linarith only [h169, h181, hlam]
                · linarith only [h181, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
          · linarith only [h184, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h186 | h186
            · rcases p0_3 (m.d 0 6) (by simp) with h187 | h187
              · linarith only [h170, h187, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h189 | h189
                · linarith only [h169, h189, hlam]
                · linarith only [h170, h189, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h192 | h192
              · linarith only [h170, h192, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h194 | h194
                · linarith only [h169, h194, hlam]
                · linarith only [h170, h194, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h197 | h197
        · rcases p0_3 (m.d 0 4) (by simp) with h198 | h198
          · linarith only [h198, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h200 | h200
            · rcases p0_3 (m.d 0 6) (by simp) with h201 | h201
              · linarith only [h169, h201, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h203 | h203
                · rcases m.htr 0 1 3 (by decide) (by decide) with h204 | h204
                  · linarith only [h197, h204, hlam]
                  · linarith only [h169, h203, h204, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h169, h203, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h208 | h208
              · linarith only [h169, h208, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h210 | h210
                · rcases m.htr 0 1 3 (by decide) (by decide) with h211 | h211
                  · linarith only [h197, h211, hlam]
                  · linarith only [h169, h210, h211, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h169, h210, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h215 | h215
          · linarith only [h215, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h217 | h217
            · rcases p0_3 (m.d 0 6) (by simp) with h218 | h218
              · linarith only [h169, h218, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h220 | h220
                · rcases m.htr 0 1 3 (by decide) (by decide) with h221 | h221
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h222 | h222
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h223 | h223
                      · linarith only [h217, h223, hlam]
                      · linarith only [h169, h220, h223, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h222, hlam, p0_0]
                  · linarith only [h169, h220, h221, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h169, h220, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h229 | h229
              · linarith only [h169, h229, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h231 | h231
                · rcases m.htr 0 1 3 (by decide) (by decide) with h232 | h232
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h233 | h233
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h234 | h234
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h235 | h235
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h236 | h236
                          · linarith only [h169, h236, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h238 | h238
                            · linarith only [h169, h238, hlam]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h240 | h240
                              · linarith only [h197, h236, h240, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h242 | h242
                                · linarith only [h197, h236, h242, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h242, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                        · linarith only [h197, h235, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h169, h231, h234, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h233, hlam, p0_0]
                  · linarith only [h169, h231, h232, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h169, h231, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h168, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h251 | h251
    · rcases p0_3 (m.d 0 2) (by simp) with h252 | h252
      · rcases p0_3 (m.d 0 3) (by simp) with h253 | h253
        · rcases p0_3 (m.d 0 4) (by simp) with h254 | h254
          · rcases p0_3 (m.d 0 5) (by simp) with h255 | h255
            · linarith only [h255, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h257 | h257
              · linarith only [h257, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h259 | h259
                · linarith only [h252, h259, hlam]
                · linarith only [h259, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h262 | h262
            · linarith only [h262, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h264 | h264
              · linarith only [h254, h264, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h266 | h266
                · linarith only [h252, h266, hlam]
                · linarith only [h254, h266, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h269 | h269
          · rcases p0_3 (m.d 0 5) (by simp) with h270 | h270
            · linarith only [h270, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h272 | h272
              · linarith only [h253, h272, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h274 | h274
                · linarith only [h252, h274, hlam]
                · linarith only [h253, h274, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h277 | h277
            · linarith only [h277, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h279 | h279
              · linarith only [h253, h279, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h281 | h281
                · linarith only [h252, h281, hlam]
                · linarith only [h253, h281, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h284 | h284
        · rcases p0_3 (m.d 0 4) (by simp) with h285 | h285
          · rcases p0_3 (m.d 0 5) (by simp) with h286 | h286
            · linarith only [h286, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h288 | h288
              · linarith only [h252, h288, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h290 | h290
                · rcases m.htr 0 1 3 (by decide) (by decide) with h291 | h291
                  · linarith only [h284, h291, hlam]
                  · linarith only [h252, h290, h291, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h252, h290, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
            · linarith only [h295, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h297 | h297
              · linarith only [h252, h297, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h299 | h299
                · rcases m.htr 0 1 3 (by decide) (by decide) with h300 | h300
                  · linarith only [h284, h300, hlam]
                  · linarith only [h252, h299, h300, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h252, h299, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h304 | h304
          · rcases p0_3 (m.d 0 5) (by simp) with h305 | h305
            · linarith only [h305, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h307 | h307
              · linarith only [h252, h307, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
                · rcases m.htr 0 1 3 (by decide) (by decide) with h310 | h310
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h311 | h311
                    · linarith only [h304, h311, hlam]
                    · linarith only [h252, h309, h311, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h252, h309, h310, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h252, h309, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h316 | h316
            · linarith only [h316, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h318 | h318
              · linarith only [h252, h318, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h320 | h320
                · rcases m.htr 0 1 3 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h322 | h322
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h323 | h323
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h324 | h324
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h325 | h325
                          · linarith only [h252, h325, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h327 | h327
                            · linarith only [h284, h325, h327, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h329 | h329
                              · linarith only [h252, h329, hlam]
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h331 | h331
                                · linarith only [h284, h325, h331, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h331, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                        · linarith only [h284, h324, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h323, hlam, p0_0]
                    · linarith only [h252, h320, h322, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h252, h320, h321, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h252, h320, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h251, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h340 | h340
    · rcases p0_3 (m.d 0 2) (by simp) with h341 | h341
      · rcases p0_3 (m.d 0 3) (by simp) with h342 | h342
        · rcases p0_3 (m.d 0 4) (by simp) with h343 | h343
          · rcases p0_3 (m.d 0 5) (by simp) with h344 | h344
            · rcases p0_3 (m.d 0 6) (by simp) with h345 | h345
              · linarith only [h345, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h347 | h347
                · linarith only [h341, h347, hlam]
                · linarith only [h347, hc06, hc12, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h350 | h350
              · linarith only [h350, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h352 | h352
                · linarith only [h341, h352, hlam]
                · linarith only [h344, h352, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h355 | h355
            · rcases p0_3 (m.d 0 6) (by simp) with h356 | h356
              · linarith only [h356, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h358 | h358
                · linarith only [h341, h358, hlam]
                · linarith only [h343, h358, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h361 | h361
              · linarith only [h361, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h363 | h363
                · linarith only [h341, h363, hlam]
                · linarith only [h343, h363, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h366 | h366
          · rcases p0_3 (m.d 0 5) (by simp) with h367 | h367
            · rcases p0_3 (m.d 0 6) (by simp) with h368 | h368
              · linarith only [h368, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h370 | h370
                · linarith only [h341, h370, hlam]
                · linarith only [h342, h370, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h373 | h373
              · linarith only [h373, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h375 | h375
                · linarith only [h341, h375, hlam]
                · linarith only [h342, h375, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h378 | h378
            · rcases p0_3 (m.d 0 6) (by simp) with h379 | h379
              · linarith only [h379, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h381 | h381
                · linarith only [h341, h381, hlam]
                · linarith only [h342, h381, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h384 | h384
              · linarith only [h384, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h386 | h386
                · linarith only [h341, h386, hlam]
                · linarith only [h342, h386, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h389 | h389
        · rcases p0_3 (m.d 0 4) (by simp) with h390 | h390
          · rcases p0_3 (m.d 0 5) (by simp) with h391 | h391
            · rcases p0_3 (m.d 0 6) (by simp) with h392 | h392
              · linarith only [h392, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h394 | h394
                · rcases m.htr 0 1 3 (by decide) (by decide) with h395 | h395
                  · linarith only [h389, h395, hlam]
                  · linarith only [h341, h394, h395, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h341, h394, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h399 | h399
              · linarith only [h399, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h401 | h401
                · rcases m.htr 0 1 3 (by decide) (by decide) with h402 | h402
                  · linarith only [h389, h402, hlam]
                  · linarith only [h341, h401, h402, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h341, h401, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h406 | h406
            · rcases p0_3 (m.d 0 6) (by simp) with h407 | h407
              · linarith only [h407, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h409 | h409
                · rcases m.htr 0 1 3 (by decide) (by decide) with h410 | h410
                  · linarith only [h389, h410, hlam]
                  · linarith only [h341, h409, h410, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h341, h409, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h414 | h414
              · linarith only [h414, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h416 | h416
                · rcases m.htr 0 1 3 (by decide) (by decide) with h417 | h417
                  · linarith only [h389, h417, hlam]
                  · linarith only [h341, h416, h417, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h341, h416, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h421 | h421
          · rcases p0_3 (m.d 0 5) (by simp) with h422 | h422
            · rcases p0_3 (m.d 0 6) (by simp) with h423 | h423
              · linarith only [h423, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h425 | h425
                · rcases m.htr 0 1 3 (by decide) (by decide) with h426 | h426
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h427 | h427
                    · linarith only [h421, h427, hlam]
                    · linarith only [h341, h425, h427, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h341, h425, h426, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h341, h425, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h432 | h432
              · linarith only [h432, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h434 | h434
                · rcases m.htr 0 1 3 (by decide) (by decide) with h435 | h435
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h436 | h436
                    · linarith only [h421, h436, hlam]
                    · linarith only [h341, h434, h436, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h341, h434, h435, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h341, h434, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h441 | h441
            · rcases p0_3 (m.d 0 6) (by simp) with h442 | h442
              · linarith only [h442, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h444 | h444
                · rcases m.htr 0 1 3 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h446 | h446
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h447 | h447
                      · linarith only [h441, h447, hlam]
                      · linarith only [h341, h444, h447, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h341, h444, h446, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h341, h444, h445, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h341, h444, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h453 | h453
              · linarith only [h453, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h455 | h455
                · rcases m.htr 0 1 3 (by decide) (by decide) with h456 | h456
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h457 | h457
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h458 | h458
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h459 | h459
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h460 | h460
                          · linarith only [h341, h460, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h462 | h462
                            · linarith only [h389, h460, h462, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h464 | h464
                              · linarith only [h389, h460, h464, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h466 | h466
                                · linarith only [h341, h466, hlam]
                                · linarith only [h466, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                        · linarith only [h459, hlam, p0_0]
                      · linarith only [h389, h458, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h341, h455, h457, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h341, h455, h456, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h341, h455, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h340, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h475 | h475
    · linarith only [h475, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h477 | h477
      · rcases p0_3 (m.d 0 3) (by simp) with h478 | h478
        · rcases p0_3 (m.d 0 4) (by simp) with h479 | h479
          · rcases p0_3 (m.d 0 5) (by simp) with h480 | h480
            · rcases p0_3 (m.d 0 6) (by simp) with h481 | h481
              · linarith only [h481, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h483 | h483
                · linarith only [h483, hlam, p0_0]
                · linarith only [h483, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h486 | h486
              · linarith only [h486, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h488 | h488
                · linarith only [h488, hlam, p0_0]
                · linarith only [h488, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h491 | h491
            · rcases p0_3 (m.d 0 6) (by simp) with h492 | h492
              · linarith only [h492, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h494 | h494
                · linarith only [h494, hlam, p0_0]
                · linarith only [h494, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h497 | h497
              · linarith only [h497, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h499 | h499
                · linarith only [h499, hlam, p0_0]
                · linarith only [h499, hc01, hc12, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h502 | h502
          · rcases p0_3 (m.d 0 5) (by simp) with h503 | h503
            · rcases p0_3 (m.d 0 6) (by simp) with h504 | h504
              · linarith only [h504, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h506 | h506
                · linarith only [h506, hlam, p0_0]
                · linarith only [h506, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h509 | h509
              · linarith only [h509, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h511 | h511
                · linarith only [h511, hlam, p0_0]
                · linarith only [h511, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h514 | h514
            · rcases p0_3 (m.d 0 6) (by simp) with h515 | h515
              · linarith only [h515, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h517 | h517
                · linarith only [h517, hlam, p0_0]
                · linarith only [h517, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h520 | h520
              · linarith only [h520, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h522 | h522
                · linarith only [h522, hlam, p0_0]
                · linarith only [h522, hc01, hc12, hlam, hphi, p0_1]
      · linarith only [h477, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h527 | h527
    · rcases p0_3 (m.d 0 2) (by simp) with h528 | h528
      · rcases p0_3 (m.d 0 3) (by simp) with h529 | h529
        · linarith only [h529, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h531 | h531
          · rcases p0_3 (m.d 0 5) (by simp) with h532 | h532
            · rcases p0_3 (m.d 0 6) (by simp) with h533 | h533
              · linarith only [h533, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h535 | h535
                · rcases m.htr 0 1 3 (by decide) (by decide) with h536 | h536
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h537 | h537
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h538 | h538
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h539 | h539
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h540 | h540
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h541 | h541
                            · linarith only [h531, h541, hlam]
                            · linarith only [h536, h541, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h540, hlam, p0_0]
                        · linarith only [h539, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h535, h536, h538, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h535, h536, h537, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h535, h536, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h527, h535, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h550 | h550
              · linarith only [h550, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h552 | h552
                · rcases m.htr 0 1 3 (by decide) (by decide) with h553 | h553
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h554 | h554
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h555 | h555
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h556 | h556
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h557 | h557
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h558 | h558
                            · linarith only [h531, h558, hlam]
                            · linarith only [h553, h558, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h557, hlam, p0_0]
                        · linarith only [h556, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h552, h553, h555, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h552, h553, h554, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h552, h553, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h527, h552, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h567 | h567
            · rcases p0_3 (m.d 0 6) (by simp) with h568 | h568
              · linarith only [h568, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h570 | h570
                · rcases m.htr 0 1 3 (by decide) (by decide) with h571 | h571
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h572 | h572
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h573 | h573
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h574 | h574
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h575 | h575
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h576 | h576
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h577 | h577
                              · linarith only [h567, h577, hlam]
                              · linarith only [h571, h577, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h571, h576, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h575, hlam, p0_0]
                        · linarith only [h574, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h570, h571, h573, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h570, h571, h572, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h570, h571, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h527, h570, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h587 | h587
              · linarith only [h587, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h589 | h589
                · rcases m.htr 0 1 3 (by decide) (by decide) with h590 | h590
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h591 | h591
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h592 | h592
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h593 | h593
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h594 | h594
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h595 | h595
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h596 | h596
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h597 | h597
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h598 | h598
                                  · linarith only [h589, h598, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h531, h598, hlam]
                                · linarith only [h597, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h590, h596, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h590, h595, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h594, hlam, p0_0]
                        · linarith only [h589, h590, h593, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h589, h590, h592, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h589, h590, h591, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h589, h590, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h527, h589, hlam]
      · linarith only [h528, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h611 | h611
      · rcases p0_3 (m.d 0 3) (by simp) with h612 | h612
        · linarith only [h612, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h614 | h614
          · rcases p0_3 (m.d 0 5) (by simp) with h615 | h615
            · rcases p0_3 (m.d 0 6) (by simp) with h616 | h616
              · linarith only [h527, h616, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h618 | h618
                · linarith only [h527, h618, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h527, h618, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h621 | h621
              · linarith only [h527, h621, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h623 | h623
                · linarith only [h527, h623, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h527, h623, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h626 | h626
            · rcases p0_3 (m.d 0 6) (by simp) with h627 | h627
              · linarith only [h527, h627, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h629 | h629
                · linarith only [h527, h629, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h527, h629, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h632 | h632
              · linarith only [h527, h632, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h634 | h634
                · linarith only [h527, h634, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h527, h634, hc01, hc12, hlam, hphi, p0_1]
      · linarith only [h611, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h638 | h638
    · rcases p0_3 (m.d 0 2) (by simp) with h639 | h639
      · rcases p0_3 (m.d 0 3) (by simp) with h640 | h640
        · rcases p0_3 (m.d 0 4) (by simp) with h641 | h641
          · linarith only [h641, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h643 | h643
            · rcases p0_3 (m.d 0 6) (by simp) with h644 | h644
              · linarith only [h644, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h646 | h646
                · rcases m.htr 0 1 3 (by decide) (by decide) with h647 | h647
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h648 | h648
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h649 | h649
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h650 | h650
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h651 | h651
                          · linarith only [h640, h651, hlam]
                          · linarith only [h648, h651, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h650, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h646, h648, h649, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h646, h648, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h646, h647, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h638, h646, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h659 | h659
              · linarith only [h659, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h661 | h661
                · rcases m.htr 0 1 3 (by decide) (by decide) with h662 | h662
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h663 | h663
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h664 | h664
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h665 | h665
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h666 | h666
                          · linarith only [h640, h666, hlam]
                          · linarith only [h663, h666, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h665, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h661, h663, h664, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h661, h663, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h661, h662, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h638, h661, hlam]
        · rcases p0_3 (m.d 0 4) (by simp) with h674 | h674
          · linarith only [h674, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h676 | h676
            · rcases p0_3 (m.d 0 6) (by simp) with h677 | h677
              · linarith only [h640, h677, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h679 | h679
                · rcases m.htr 0 1 3 (by decide) (by decide) with h680 | h680
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h681 | h681
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h682 | h682
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h683 | h683
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h684 | h684
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h685 | h685
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h686 | h686
                              · linarith only [h676, h686, hlam]
                              · linarith only [h640, h680, h686, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h685, hlam, p0_0]
                          · linarith only [h640, h680, h684, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h683, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h640, h679, h680, h682, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h640, h679, h680, h681, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h640, h679, h680, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h638, h679, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h696 | h696
              · linarith only [h640, h696, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h698 | h698
                · rcases m.htr 0 1 3 (by decide) (by decide) with h699 | h699
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h700 | h700
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h701 | h701
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h702 | h702
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h703 | h703
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h704 | h704
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h705 | h705
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h706 | h706
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h707 | h707
                                  · linarith only [h640, h707, hlam]
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h709 | h709
                                    · linarith only [h698, h707, h709, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h711 | h711
                                      · linarith only [h698, h707, h711, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                      · linarith only [h711, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                · linarith only [h640, h699, h706, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h640, h699, h705, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h704, hlam, p0_0]
                          · linarith only [h640, h699, h703, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h640, h698, h699, h702, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h640, h698, h699, h701, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h640, h698, h699, h700, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h640, h698, h699, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h638, h698, hlam]
      · linarith only [h639, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h724 | h724
      · rcases p0_3 (m.d 0 3) (by simp) with h725 | h725
        · rcases p0_3 (m.d 0 4) (by simp) with h726 | h726
          · linarith only [h726, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h728 | h728
            · rcases p0_3 (m.d 0 6) (by simp) with h729 | h729
              · linarith only [h638, h729, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h731 | h731
                · linarith only [h638, h731, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h638, h731, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h734 | h734
              · linarith only [h638, h734, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h736 | h736
                · linarith only [h638, h736, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h638, h736, hc01, hc12, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h739 | h739
          · linarith only [h739, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h741 | h741
            · rcases p0_3 (m.d 0 6) (by simp) with h742 | h742
              · linarith only [h638, h742, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h744 | h744
                · linarith only [h638, h744, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h638, h744, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h747 | h747
              · linarith only [h638, h747, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h749 | h749
                · linarith only [h638, h749, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h638, h749, hc01, hc12, hlam, hphi, p0_1]
      · linarith only [h724, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h753 | h753
    · rcases p0_3 (m.d 0 2) (by simp) with h754 | h754
      · rcases p0_3 (m.d 0 3) (by simp) with h755 | h755
        · rcases p0_3 (m.d 0 4) (by simp) with h756 | h756
          · rcases p0_3 (m.d 0 5) (by simp) with h757 | h757
            · linarith only [h757, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h759 | h759
              · linarith only [h759, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h761 | h761
                · rcases m.htr 0 1 3 (by decide) (by decide) with h762 | h762
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h763 | h763
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h764 | h764
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h765 | h765
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h766 | h766
                          · linarith only [h755, h766, hlam]
                          · linarith only [h764, h766, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                        · linarith only [h765, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h761, h764, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h761, h763, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h761, h762, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h753, h761, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h774 | h774
            · linarith only [h774, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h776 | h776
              · linarith only [h756, h776, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h778 | h778
                · rcases m.htr 0 1 3 (by decide) (by decide) with h779 | h779
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h780 | h780
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h781 | h781
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h782 | h782
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h783 | h783
                          · linarith only [h755, h783, hlam]
                          · linarith only [h756, h780, h783, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h782, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h756, h778, h780, h781, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h756, h778, h780, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h756, h778, h779, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h753, h778, hlam]
        · rcases p0_3 (m.d 0 4) (by simp) with h791 | h791
          · rcases p0_3 (m.d 0 5) (by simp) with h792 | h792
            · linarith only [h792, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h794 | h794
              · linarith only [h755, h794, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h796 | h796
                · rcases m.htr 0 1 3 (by decide) (by decide) with h797 | h797
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h798 | h798
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h799 | h799
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h800 | h800
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h801 | h801
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h802 | h802
                            · linarith only [h791, h802, hlam]
                            · linarith only [h755, h797, h802, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h755, h797, h801, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h800, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h755, h796, h797, h799, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h755, h796, h797, h798, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h755, h796, h797, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h753, h796, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h811 | h811
            · linarith only [h811, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h813 | h813
              · linarith only [h755, h813, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h815 | h815
                · rcases m.htr 0 1 3 (by decide) (by decide) with h816 | h816
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h817 | h817
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h818 | h818
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h819 | h819
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h820 | h820
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h821 | h821
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h822 | h822
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h823 | h823
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h824 | h824
                                  · linarith only [h755, h815, h824, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h826 | h826
                                    · linarith only [h755, h826, hlam]
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h828 | h828
                                      · linarith only [h791, h815, h824, h828, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                      · linarith only [h828, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                · linarith only [h791, h823, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h822, hlam, p0_0]
                            · linarith only [h755, h816, h821, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h755, h816, h820, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h755, h815, h816, h819, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h755, h815, h816, h818, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h755, h815, h816, h817, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h755, h815, h816, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h753, h815, hlam]
      · linarith only [h754, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h841 | h841
      · rcases p0_3 (m.d 0 3) (by simp) with h842 | h842
        · rcases p0_3 (m.d 0 4) (by simp) with h843 | h843
          · rcases p0_3 (m.d 0 5) (by simp) with h844 | h844
            · linarith only [h844, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h846 | h846
              · linarith only [h753, h846, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h848 | h848
                · linarith only [h753, h848, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h753, h848, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h851 | h851
            · linarith only [h851, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h853 | h853
              · linarith only [h753, h853, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h855 | h855
                · linarith only [h753, h855, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h753, h855, hc01, hc12, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h858 | h858
          · rcases p0_3 (m.d 0 5) (by simp) with h859 | h859
            · linarith only [h859, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h861 | h861
              · linarith only [h753, h861, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h863 | h863
                · linarith only [h753, h863, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h753, h863, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h866 | h866
            · linarith only [h866, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h868 | h868
              · linarith only [h753, h868, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h870 | h870
                · linarith only [h753, h870, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h753, h870, hc01, hc12, hlam, hphi, p0_1]
      · linarith only [h841, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h874 | h874
    · rcases p0_3 (m.d 0 2) (by simp) with h875 | h875
      · rcases p0_3 (m.d 0 3) (by simp) with h876 | h876
        · rcases p0_3 (m.d 0 4) (by simp) with h877 | h877
          · rcases p0_3 (m.d 0 5) (by simp) with h878 | h878
            · rcases p0_3 (m.d 0 6) (by simp) with h879 | h879
              · linarith only [h879, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h881 | h881
                · rcases m.htr 0 1 3 (by decide) (by decide) with h882 | h882
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h883 | h883
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h884 | h884
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h885 | h885
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h886 | h886
                          · linarith only [h876, h886, hlam]
                          · linarith only [h886, hc06, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                        · linarith only [h885, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h881, h884, hc06, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                    · linarith only [h881, h883, hc06, hc14, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                  · linarith only [h881, h882, hc06, hc13, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                · linarith only [h874, h881, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h894 | h894
              · linarith only [h894, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h896 | h896
                · rcases m.htr 0 1 3 (by decide) (by decide) with h897 | h897
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h898 | h898
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h899 | h899
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h900 | h900
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h901 | h901
                          · linarith only [h876, h901, hlam]
                          · linarith only [h878, h899, h901, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                        · linarith only [h900, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h878, h896, h899, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h878, h896, h898, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h878, h896, h897, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h874, h896, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h909 | h909
            · rcases p0_3 (m.d 0 6) (by simp) with h910 | h910
              · linarith only [h910, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h912 | h912
                · rcases m.htr 0 1 3 (by decide) (by decide) with h913 | h913
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h914 | h914
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h915 | h915
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h916 | h916
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h917 | h917
                          · linarith only [h876, h917, hlam]
                          · linarith only [h877, h914, h917, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h877, h912, h914, h915, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h877, h912, h914, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h877, h912, h913, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h912, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h925 | h925
              · linarith only [h925, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h927 | h927
                · rcases m.htr 0 1 3 (by decide) (by decide) with h928 | h928
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h929 | h929
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h930 | h930
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h931 | h931
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h932 | h932
                          · linarith only [h876, h932, hlam]
                          · linarith only [h877, h929, h932, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h931, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h877, h927, h929, h930, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h877, h927, h929, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h877, h927, h928, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h927, hlam]
        · rcases p0_3 (m.d 0 4) (by simp) with h940 | h940
          · rcases p0_3 (m.d 0 5) (by simp) with h941 | h941
            · rcases p0_3 (m.d 0 6) (by simp) with h942 | h942
              · linarith only [h942, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h944 | h944
                · rcases m.htr 0 1 3 (by decide) (by decide) with h945 | h945
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h946 | h946
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h947 | h947
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h948 | h948
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h949 | h949
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h950 | h950
                            · linarith only [h940, h950, hlam]
                            · linarith only [h876, h945, h950, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h876, h945, h949, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h948, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h876, h944, h945, h947, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h876, h944, h945, h946, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h876, h944, h945, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h944, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h959 | h959
              · linarith only [h959, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h961 | h961
                · rcases m.htr 0 1 3 (by decide) (by decide) with h962 | h962
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h963 | h963
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h964 | h964
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h965 | h965
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h966 | h966
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h967 | h967
                            · linarith only [h940, h967, hlam]
                            · linarith only [h876, h962, h967, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h876, h962, h966, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h965, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h876, h961, h962, h964, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h876, h961, h962, h963, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h876, h961, h962, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h961, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h976 | h976
            · rcases p0_3 (m.d 0 6) (by simp) with h977 | h977
              · linarith only [h977, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h979 | h979
                · rcases m.htr 0 1 3 (by decide) (by decide) with h980 | h980
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h981 | h981
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h982 | h982
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h983 | h983
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h984 | h984
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h985 | h985
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h986 | h986
                              · linarith only [h976, h986, hlam]
                              · linarith only [h876, h980, h986, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h876, h980, h985, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h876, h980, h984, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h983, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h876, h979, h980, h982, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h876, h979, h980, h981, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h876, h979, h980, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h979, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h996 | h996
              · linarith only [h996, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h998 | h998
                · rcases m.htr 0 1 3 (by decide) (by decide) with h999 | h999
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1000 | h1000
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1001 | h1001
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1002 | h1002
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1003 | h1003
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1004 | h1004
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1005 | h1005
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1006 | h1006
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1007 | h1007
                                  · linarith only [h1007, h876, h998, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1009 | h1009
                                    · linarith only [h1007, h1009, h940, h998, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1011 | h1011
                                      · linarith only [h1011, h876, hlam]
                                      · linarith only [h1011, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                · linarith only [h1006, hlam, p0_0]
                              · linarith only [h1005, h876, h999, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1004, h876, h999, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1003, h876, h999, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1002, h876, h998, h999, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1001, h876, h998, h999, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1000, h876, h998, h999, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h876, h998, h999, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h874, h998, hlam]
      · linarith only [h875, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1024 | h1024
      · rcases p0_3 (m.d 0 3) (by simp) with h1025 | h1025
        · rcases p0_3 (m.d 0 4) (by simp) with h1026 | h1026
          · rcases p0_3 (m.d 0 5) (by simp) with h1027 | h1027
            · rcases p0_3 (m.d 0 6) (by simp) with h1028 | h1028
              · linarith only [h1028, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1030 | h1030
                · linarith only [h1030, h874, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1030, h874, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1033 | h1033
              · linarith only [h1033, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1035 | h1035
                · linarith only [h1035, h874, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1035, h874, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1038 | h1038
            · rcases p0_3 (m.d 0 6) (by simp) with h1039 | h1039
              · linarith only [h1039, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1041 | h1041
                · linarith only [h1041, h874, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1041, h874, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1044 | h1044
              · linarith only [h1044, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1046 | h1046
                · linarith only [h1046, h874, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1046, h874, hc01, hc12, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h1049 | h1049
          · rcases p0_3 (m.d 0 5) (by simp) with h1050 | h1050
            · rcases p0_3 (m.d 0 6) (by simp) with h1051 | h1051
              · linarith only [h1051, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1053 | h1053
                · linarith only [h1053, h874, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1053, h874, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1056 | h1056
              · linarith only [h1056, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1058 | h1058
                · linarith only [h1058, h874, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1058, h874, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1061 | h1061
            · rcases p0_3 (m.d 0 6) (by simp) with h1062 | h1062
              · linarith only [h1062, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1064 | h1064
                · linarith only [h1064, h874, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1064, h874, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1067 | h1067
              · linarith only [h1067, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1069 | h1069
                · linarith only [h1069, h874, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1069, h874, hc01, hc12, hlam, hphi, p0_1]
      · linarith only [h1024, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1073 | h1073
    · linarith only [h1073, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1075 | h1075
      · rcases p0_3 (m.d 0 3) (by simp) with h1076 | h1076
        · rcases p0_3 (m.d 0 4) (by simp) with h1077 | h1077
          · rcases p0_3 (m.d 0 5) (by simp) with h1078 | h1078
            · rcases p0_3 (m.d 0 6) (by simp) with h1079 | h1079
              · linarith only [h1079, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1081 | h1081
                · linarith only [h1075, h1081, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1075, h1081, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1084 | h1084
              · linarith only [h1084, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1086 | h1086
                · linarith only [h1075, h1086, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1075, h1086, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1089 | h1089
            · rcases p0_3 (m.d 0 6) (by simp) with h1090 | h1090
              · linarith only [h1090, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1092 | h1092
                · linarith only [h1075, h1092, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1075, h1092, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1095 | h1095
              · linarith only [h1095, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1097 | h1097
                · linarith only [h1075, h1097, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1075, h1097, hc01, hc12, hlam, hphi, p0_1]
        · linarith only [h1076, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1101 | h1101
        · rcases p0_3 (m.d 0 4) (by simp) with h1102 | h1102
          · rcases p0_3 (m.d 0 5) (by simp) with h1103 | h1103
            · rcases p0_3 (m.d 0 6) (by simp) with h1104 | h1104
              · linarith only [h1104, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1106 | h1106
                · linarith only [h1106, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1075, h1106, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h1109 | h1109
              · linarith only [h1109, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1111 | h1111
                · linarith only [h1111, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1075, h1111, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h1114 | h1114
            · rcases p0_3 (m.d 0 6) (by simp) with h1115 | h1115
              · linarith only [h1115, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1117 | h1117
                · linarith only [h1117, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1075, h1117, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h1120 | h1120
              · linarith only [h1120, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1122 | h1122
                · linarith only [h1122, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1075, h1122, hlam]
        · linarith only [h1101, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1126 | h1126
    · rcases p0_3 (m.d 0 2) (by simp) with h1127 | h1127
      · linarith only [h1127, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1129 | h1129
        · rcases p0_3 (m.d 0 4) (by simp) with h1130 | h1130
          · rcases p0_3 (m.d 0 5) (by simp) with h1131 | h1131
            · rcases p0_3 (m.d 0 6) (by simp) with h1132 | h1132
              · linarith only [h1132, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1134 | h1134
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1135 | h1135
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1136 | h1136
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1137 | h1137
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1138 | h1138
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1139 | h1139
                          · linarith only [h1139, hlam, p0_0]
                          · linarith only [h1134, h1139, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h1134, h1135, h1138, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1134, h1135, h1137, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1134, h1135, h1136, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1126, h1135, hlam]
                · linarith only [h1126, h1134, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1147 | h1147
              · linarith only [h1147, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1149 | h1149
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1150 | h1150
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1151 | h1151
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1152 | h1152
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1153 | h1153
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1154 | h1154
                          · linarith only [h1154, hlam, p0_0]
                          · linarith only [h1149, h1154, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h1149, h1150, h1153, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1149, h1150, h1152, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1149, h1150, h1151, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1126, h1150, hlam]
                · linarith only [h1126, h1149, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1162 | h1162
            · rcases p0_3 (m.d 0 6) (by simp) with h1163 | h1163
              · linarith only [h1163, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1165 | h1165
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1166 | h1166
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1167 | h1167
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1168 | h1168
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1169 | h1169
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1170 | h1170
                          · linarith only [h1170, hlam, p0_0]
                          · linarith only [h1165, h1170, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h1165, h1166, h1169, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1165, h1166, h1168, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1165, h1166, h1167, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1126, h1166, hlam]
                · linarith only [h1126, h1165, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1178 | h1178
              · linarith only [h1178, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1180 | h1180
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1181 | h1181
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1182 | h1182
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1183 | h1183
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1184 | h1184
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1185 | h1185
                          · linarith only [h1185, hlam, p0_0]
                          · linarith only [h1180, h1185, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h1180, h1181, h1184, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1180, h1181, h1183, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1180, h1181, h1182, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1126, h1181, hlam]
                · linarith only [h1126, h1180, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · linarith only [h1129, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1194 | h1194
      · linarith only [h1194, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1196 | h1196
        · rcases p0_3 (m.d 0 4) (by simp) with h1197 | h1197
          · rcases p0_3 (m.d 0 5) (by simp) with h1198 | h1198
            · rcases p0_3 (m.d 0 6) (by simp) with h1199 | h1199
              · linarith only [h1126, h1199, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1201 | h1201
                · linarith only [h1126, h1201, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1203 | h1203
                  · linarith only [h1201, h1203, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1201, h1203, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1206 | h1206
              · linarith only [h1126, h1206, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1208 | h1208
                · linarith only [h1126, h1208, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1210 | h1210
                  · linarith only [h1208, h1210, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1208, h1210, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1213 | h1213
            · rcases p0_3 (m.d 0 6) (by simp) with h1214 | h1214
              · linarith only [h1126, h1214, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1216 | h1216
                · linarith only [h1126, h1216, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1218 | h1218
                  · linarith only [h1216, h1218, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1216, h1218, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1221 | h1221
              · linarith only [h1221, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1223 | h1223
                · linarith only [h1126, h1223, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1225 | h1225
                  · linarith only [h1223, h1225, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1223, h1225, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h1196, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1230 | h1230
    · rcases p0_3 (m.d 0 2) (by simp) with h1231 | h1231
      · rcases p0_3 (m.d 0 3) (by simp) with h1232 | h1232
        · rcases p0_3 (m.d 0 4) (by simp) with h1233 | h1233
          · linarith only [h1233, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1235 | h1235
            · rcases p0_3 (m.d 0 6) (by simp) with h1236 | h1236
              · linarith only [h1236, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1238 | h1238
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1239 | h1239
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1240 | h1240
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1241 | h1241
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1242 | h1242
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1243 | h1243
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1244 | h1244
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1245 | h1245
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1246 | h1246
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1247 | h1247
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1248 | h1248
                                    · linarith only [h1235, h1248, hlam]
                                    · linarith only [h1240, h1248, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h1247, hlam, p0_0]
                                · linarith only [h1246, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1240, h1243, h1245, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1240, h1243, h1244, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1231, h1243, hlam]
                        · linarith only [h1242, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1239, h1240, h1241, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1239, h1240, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1230, h1239, hlam]
                · linarith only [h1230, h1238, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1261 | h1261
              · linarith only [h1261, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1263 | h1263
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1264 | h1264
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1265 | h1265
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1266 | h1266
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1267 | h1267
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1268 | h1268
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1269 | h1269
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1270 | h1270
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1271 | h1271
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1272 | h1272
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1273 | h1273
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1274 | h1274
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1275 | h1275
                                        · linarith only [h1263, h1268, h1275, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                        · linarith only [h1235, h1275, hlam]
                                      · linarith only [h1274, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h1265, h1273, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h1272, hlam, p0_0]
                                · linarith only [h1265, h1268, h1271, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1265, h1268, h1270, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1265, h1268, h1269, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1231, h1268, hlam]
                        · linarith only [h1267, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1264, h1265, h1266, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1264, h1265, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1230, h1264, hlam]
                · linarith only [h1230, h1263, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · linarith only [h1232, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1291 | h1291
        · rcases p0_3 (m.d 0 4) (by simp) with h1292 | h1292
          · linarith only [h1292, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1294 | h1294
            · rcases p0_3 (m.d 0 6) (by simp) with h1295 | h1295
              · linarith only [h1231, h1295, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1297 | h1297
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1298 | h1298
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1299 | h1299
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1300 | h1300
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1301 | h1301
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1302 | h1302
                          · linarith only [h1231, h1298, h1302, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1231, h1302, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1231, h1297, h1298, h1301, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1231, h1297, h1298, h1300, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1231, h1297, h1298, h1299, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1230, h1298, hlam]
                · linarith only [h1230, h1231, h1297, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1310 | h1310
              · linarith only [h1231, h1310, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1312 | h1312
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1313 | h1313
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1314 | h1314
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1315 | h1315
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1316 | h1316
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1317 | h1317
                          · linarith only [h1231, h1313, h1317, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1231, h1317, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1231, h1312, h1313, h1316, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1231, h1312, h1313, h1315, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1231, h1312, h1313, h1314, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1230, h1313, hlam]
                · linarith only [h1230, h1231, h1312, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · linarith only [h1291, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1326 | h1326
      · rcases p0_3 (m.d 0 3) (by simp) with h1327 | h1327
        · rcases p0_3 (m.d 0 4) (by simp) with h1328 | h1328
          · linarith only [h1328, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1330 | h1330
            · rcases p0_3 (m.d 0 6) (by simp) with h1331 | h1331
              · linarith only [h1230, h1331, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1333 | h1333
                · linarith only [h1230, h1326, h1333, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1230, h1326, h1333, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1336 | h1336
              · linarith only [h1230, h1336, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1338 | h1338
                · linarith only [h1230, h1326, h1338, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1230, h1326, h1338, hc01, hc12, hlam, hphi, p0_1]
        · linarith only [h1327, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1342 | h1342
        · rcases p0_3 (m.d 0 4) (by simp) with h1343 | h1343
          · linarith only [h1343, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1345 | h1345
            · rcases p0_3 (m.d 0 6) (by simp) with h1346 | h1346
              · linarith only [h1230, h1346, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1348 | h1348
                · linarith only [h1230, h1348, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1350 | h1350
                  · linarith only [h1326, h1348, h1350, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1326, h1348, h1350, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1353 | h1353
              · linarith only [h1326, h1353, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1355 | h1355
                · linarith only [h1230, h1355, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1357 | h1357
                  · linarith only [h1326, h1355, h1357, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1326, h1355, h1357, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h1342, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1361 | h1361
    · rcases p0_3 (m.d 0 2) (by simp) with h1362 | h1362
      · rcases p0_3 (m.d 0 3) (by simp) with h1363 | h1363
        · rcases p0_3 (m.d 0 4) (by simp) with h1364 | h1364
          · rcases p0_3 (m.d 0 5) (by simp) with h1365 | h1365
            · linarith only [h1365, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1367 | h1367
              · linarith only [h1367, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1369 | h1369
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1370 | h1370
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1371 | h1371
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1372 | h1372
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1373 | h1373
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1374 | h1374
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1375 | h1375
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1376 | h1376
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1377 | h1377
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1378 | h1378
                                  · linarith only [h1364, h1378, hlam]
                                  · linarith only [h1372, h1378, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                · linarith only [h1377, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1372, h1374, h1376, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                            · linarith only [h1372, h1374, h1375, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                          · linarith only [h1362, h1374, hlam]
                        · linarith only [h1373, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1370, h1372, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h1370, h1371, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h1361, h1370, hlam]
                · linarith only [h1361, h1369, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1390 | h1390
            · linarith only [h1390, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1392 | h1392
              · linarith only [h1364, h1392, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1394 | h1394
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1395 | h1395
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1396 | h1396
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1397 | h1397
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1398 | h1398
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1399 | h1399
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1400 | h1400
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1401 | h1401
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1402 | h1402
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1403 | h1403
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1404 | h1404
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1405 | h1405
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1406 | h1406
                                        · linarith only [h1364, h1406, hlam]
                                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1408 | h1408
                                          · linarith only [h1394, h1399, h1406, h1408, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                          · linarith only [h1408, hc04, hlam, hphi, ht45, ht56, u6elo4]
                                      · linarith only [h1364, h1396, h1405, hc14, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                    · linarith only [h1404, hlam, p0_0]
                                  · linarith only [h1364, h1396, h1403, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h1364, h1396, h1399, h1402, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1364, h1396, h1399, h1401, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1364, h1396, h1399, h1400, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1362, h1399, hlam]
                        · linarith only [h1398, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1364, h1395, h1396, h1397, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1364, h1395, h1396, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1361, h1395, hlam]
                · linarith only [h1361, h1364, h1394, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · linarith only [h1363, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1424 | h1424
        · rcases p0_3 (m.d 0 4) (by simp) with h1425 | h1425
          · rcases p0_3 (m.d 0 5) (by simp) with h1426 | h1426
            · linarith only [h1426, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1428 | h1428
              · linarith only [h1362, h1428, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1430 | h1430
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1431 | h1431
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1432 | h1432
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1433 | h1433
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1434 | h1434
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1435 | h1435
                          · linarith only [h1362, h1431, h1435, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1362, h1435, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1362, h1430, h1431, h1434, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1362, h1430, h1431, h1433, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1362, h1430, h1431, h1432, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1361, h1431, hlam]
                · linarith only [h1361, h1362, h1430, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1443 | h1443
            · linarith only [h1443, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1445 | h1445
              · linarith only [h1362, h1445, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1447 | h1447
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1448 | h1448
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1449 | h1449
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1450 | h1450
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1451 | h1451
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1452 | h1452
                          · linarith only [h1362, h1448, h1452, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1362, h1452, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1362, h1447, h1448, h1451, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1362, h1447, h1448, h1450, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1362, h1447, h1448, h1449, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1361, h1448, hlam]
                · linarith only [h1361, h1362, h1447, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · linarith only [h1424, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1461 | h1461
      · rcases p0_3 (m.d 0 3) (by simp) with h1462 | h1462
        · rcases p0_3 (m.d 0 4) (by simp) with h1463 | h1463
          · rcases p0_3 (m.d 0 5) (by simp) with h1464 | h1464
            · linarith only [h1464, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1466 | h1466
              · linarith only [h1361, h1466, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1468 | h1468
                · linarith only [h1361, h1461, h1468, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1361, h1461, h1468, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1471 | h1471
            · linarith only [h1471, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1473 | h1473
              · linarith only [h1361, h1473, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1475 | h1475
                · linarith only [h1361, h1461, h1475, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1361, h1461, h1475, hc01, hc12, hlam, hphi, p0_1]
        · linarith only [h1462, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1479 | h1479
        · rcases p0_3 (m.d 0 4) (by simp) with h1480 | h1480
          · rcases p0_3 (m.d 0 5) (by simp) with h1481 | h1481
            · linarith only [h1481, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1483 | h1483
              · linarith only [h1361, h1483, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1485 | h1485
                · linarith only [h1361, h1485, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1487 | h1487
                  · linarith only [h1461, h1485, h1487, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1461, h1485, h1487, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1490 | h1490
            · linarith only [h1490, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1492 | h1492
              · linarith only [h1461, h1492, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1494 | h1494
                · linarith only [h1361, h1494, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1496 | h1496
                  · linarith only [h1461, h1494, h1496, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1461, h1494, h1496, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h1479, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1500 | h1500
    · rcases p0_3 (m.d 0 2) (by simp) with h1501 | h1501
      · rcases p0_3 (m.d 0 3) (by simp) with h1502 | h1502
        · rcases p0_3 (m.d 0 4) (by simp) with h1503 | h1503
          · rcases p0_3 (m.d 0 5) (by simp) with h1504 | h1504
            · rcases p0_3 (m.d 0 6) (by simp) with h1505 | h1505
              · linarith only [h1505, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1507 | h1507
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1508 | h1508
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1509 | h1509
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1510 | h1510
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1511 | h1511
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1512 | h1512
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1513 | h1513
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1514 | h1514
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1515 | h1515
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1516 | h1516
                                  · linarith only [h1503, h1516, hlam]
                                  · linarith only [h1516, hc06, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                                · linarith only [h1515, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1511, h1512, h1514, hc16, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                            · linarith only [h1511, h1512, h1513, hc16, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                          · linarith only [h1501, h1512, hlam]
                        · linarith only [h1511, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1508, h1510, hc06, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                    · linarith only [h1508, h1509, hc06, hc14, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                  · linarith only [h1500, h1508, hlam]
                · linarith only [h1500, h1507, hc06, hc12, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1528 | h1528
              · linarith only [h1528, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1530 | h1530
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1531 | h1531
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1532 | h1532
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1533 | h1533
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1534 | h1534
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1535 | h1535
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1536 | h1536
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1537 | h1537
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1538 | h1538
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1539 | h1539
                                  · linarith only [h1503, h1539, hlam]
                                  · linarith only [h1504, h1533, h1539, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                · linarith only [h1538, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1504, h1533, h1535, h1537, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                            · linarith only [h1504, h1533, h1535, h1536, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                          · linarith only [h1501, h1535, hlam]
                        · linarith only [h1534, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1504, h1531, h1533, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h1504, h1531, h1532, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h1500, h1531, hlam]
                · linarith only [h1500, h1504, h1530, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1551 | h1551
            · rcases p0_3 (m.d 0 6) (by simp) with h1552 | h1552
              · linarith only [h1552, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1554 | h1554
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1555 | h1555
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1556 | h1556
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1557 | h1557
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1558 | h1558
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1559 | h1559
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1560 | h1560
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1561 | h1561
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1562 | h1562
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1563 | h1563
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1564 | h1564
                                    · linarith only [h1551, h1564, hlam]
                                    · linarith only [h1503, h1556, h1564, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h1503, h1556, h1563, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h1562, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1503, h1556, h1559, h1561, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1503, h1556, h1559, h1560, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1501, h1559, hlam]
                        · linarith only [h1558, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1503, h1555, h1556, h1557, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1503, h1555, h1556, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1500, h1555, hlam]
                · linarith only [h1500, h1503, h1554, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1577 | h1577
              · linarith only [h1577, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1579 | h1579
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1580 | h1580
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1581 | h1581
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1582 | h1582
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1583 | h1583
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1584 | h1584
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1585 | h1585
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1586 | h1586
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1587 | h1587
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1588 | h1588
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1589 | h1589
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1590 | h1590
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1591 | h1591
                                        · linarith only [h1503, h1579, h1584, h1591, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1593 | h1593
                                          · linarith only [h1503, h1593, hlam]
                                          · linarith only [h1593, hc04, hlam, hphi, ht45, ht56, u6elo4]
                                      · linarith only [h1590, hlam, p0_0]
                                    · linarith only [h1503, h1581, h1589, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h1503, h1581, h1588, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h1503, h1581, h1584, h1587, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1503, h1581, h1584, h1586, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1503, h1581, h1584, h1585, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1501, h1584, hlam]
                        · linarith only [h1583, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1503, h1580, h1581, h1582, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1503, h1580, h1581, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1500, h1580, hlam]
                · linarith only [h1500, h1503, h1579, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · linarith only [h1502, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1609 | h1609
        · rcases p0_3 (m.d 0 4) (by simp) with h1610 | h1610
          · rcases p0_3 (m.d 0 5) (by simp) with h1611 | h1611
            · rcases p0_3 (m.d 0 6) (by simp) with h1612 | h1612
              · linarith only [h1612, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1614 | h1614
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1615 | h1615
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1616 | h1616
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1617 | h1617
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1618 | h1618
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1619 | h1619
                          · linarith only [h1501, h1615, h1619, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1501, h1619, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1501, h1614, h1615, h1618, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1501, h1614, h1615, h1617, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1501, h1614, h1615, h1616, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1500, h1615, hlam]
                · linarith only [h1500, h1501, h1614, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1627 | h1627
              · linarith only [h1627, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1629 | h1629
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1630 | h1630
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1631 | h1631
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1632 | h1632
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1633 | h1633
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1634 | h1634
                          · linarith only [h1501, h1630, h1634, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1501, h1634, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1501, h1629, h1630, h1633, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1501, h1629, h1630, h1632, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1501, h1629, h1630, h1631, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1500, h1630, hlam]
                · linarith only [h1500, h1501, h1629, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1642 | h1642
            · rcases p0_3 (m.d 0 6) (by simp) with h1643 | h1643
              · linarith only [h1643, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1645 | h1645
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1646 | h1646
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1647 | h1647
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1648 | h1648
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1649 | h1649
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1650 | h1650
                          · linarith only [h1501, h1646, h1650, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1501, h1650, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1501, h1645, h1646, h1649, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1501, h1645, h1646, h1648, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1501, h1645, h1646, h1647, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1500, h1646, hlam]
                · linarith only [h1500, h1501, h1645, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1658 | h1658
              · linarith only [h1658, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1660 | h1660
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1661 | h1661
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1662 | h1662
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1663 | h1663
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1664 | h1664
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1665 | h1665
                          · linarith only [h1501, h1661, h1665, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1501, h1665, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1501, h1660, h1661, h1664, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1501, h1660, h1661, h1663, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1501, h1660, h1661, h1662, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1500, h1661, hlam]
                · linarith only [h1500, h1501, h1660, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · linarith only [h1609, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1674 | h1674
      · rcases p0_3 (m.d 0 3) (by simp) with h1675 | h1675
        · rcases p0_3 (m.d 0 4) (by simp) with h1676 | h1676
          · rcases p0_3 (m.d 0 5) (by simp) with h1677 | h1677
            · rcases p0_3 (m.d 0 6) (by simp) with h1678 | h1678
              · linarith only [h1678, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1680 | h1680
                · linarith only [h1500, h1674, h1680, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1500, h1674, h1680, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1683 | h1683
              · linarith only [h1683, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1685 | h1685
                · linarith only [h1500, h1674, h1685, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1500, h1674, h1685, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1688 | h1688
            · rcases p0_3 (m.d 0 6) (by simp) with h1689 | h1689
              · linarith only [h1689, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1691 | h1691
                · linarith only [h1500, h1674, h1691, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1500, h1674, h1691, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1694 | h1694
              · linarith only [h1694, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1696 | h1696
                · linarith only [h1500, h1674, h1696, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1500, h1674, h1696, hc01, hc12, hlam, hphi, p0_1]
        · linarith only [h1675, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1700 | h1700
        · rcases p0_3 (m.d 0 4) (by simp) with h1701 | h1701
          · rcases p0_3 (m.d 0 5) (by simp) with h1702 | h1702
            · rcases p0_3 (m.d 0 6) (by simp) with h1703 | h1703
              · linarith only [h1703, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1705 | h1705
                · linarith only [h1500, h1705, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1707 | h1707
                  · linarith only [h1674, h1705, h1707, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1674, h1705, h1707, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1710 | h1710
              · linarith only [h1710, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1712 | h1712
                · linarith only [h1500, h1712, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1714 | h1714
                  · linarith only [h1674, h1712, h1714, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1674, h1712, h1714, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h1717 | h1717
            · rcases p0_3 (m.d 0 6) (by simp) with h1718 | h1718
              · linarith only [h1718, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1720 | h1720
                · linarith only [h1500, h1720, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1722 | h1722
                  · linarith only [h1674, h1720, h1722, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1674, h1720, h1722, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1725 | h1725
              · linarith only [h1725, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1727 | h1727
                · linarith only [h1500, h1727, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1729 | h1729
                  · linarith only [h1674, h1727, h1729, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1674, h1727, h1729, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h1700, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1733 | h1733
    · linarith only [h1733, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1735 | h1735
      · rcases p0_3 (m.d 0 3) (by simp) with h1736 | h1736
        · rcases p0_3 (m.d 0 4) (by simp) with h1737 | h1737
          · rcases p0_3 (m.d 0 5) (by simp) with h1738 | h1738
            · rcases p0_3 (m.d 0 6) (by simp) with h1739 | h1739
              · linarith only [h1739, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1741 | h1741
                · linarith only [h1735, h1741, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1735, h1741, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1744 | h1744
              · linarith only [h1744, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1746 | h1746
                · linarith only [h1735, h1746, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1735, h1746, hc01, hc12, hlam, hphi, p0_1]
          · linarith only [h1737, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1750 | h1750
          · rcases p0_3 (m.d 0 5) (by simp) with h1751 | h1751
            · rcases p0_3 (m.d 0 6) (by simp) with h1752 | h1752
              · linarith only [h1752, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1754 | h1754
                · linarith only [h1735, h1754, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1735, h1754, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1757 | h1757
              · linarith only [h1757, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1759 | h1759
                · linarith only [h1735, h1759, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1735, h1759, hc01, hc12, hlam, hphi, p0_1]
          · linarith only [h1750, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1763 | h1763
        · rcases p0_3 (m.d 0 4) (by simp) with h1764 | h1764
          · rcases p0_3 (m.d 0 5) (by simp) with h1765 | h1765
            · rcases p0_3 (m.d 0 6) (by simp) with h1766 | h1766
              · linarith only [h1766, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1768 | h1768
                · linarith only [h1763, h1768, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1735, h1768, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h1771 | h1771
              · linarith only [h1771, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1773 | h1773
                · linarith only [h1773, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1735, h1773, hlam]
          · linarith only [h1764, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1777 | h1777
          · rcases p0_3 (m.d 0 5) (by simp) with h1778 | h1778
            · rcases p0_3 (m.d 0 6) (by simp) with h1779 | h1779
              · linarith only [h1779, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1781 | h1781
                · linarith only [h1781, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1735, h1781, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h1784 | h1784
              · linarith only [h1784, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1786 | h1786
                · linarith only [h1786, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1735, h1786, hlam]
          · linarith only [h1777, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1790 | h1790
    · rcases p0_3 (m.d 0 2) (by simp) with h1791 | h1791
      · linarith only [h1791, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1793 | h1793
        · rcases p0_3 (m.d 0 4) (by simp) with h1794 | h1794
          · rcases p0_3 (m.d 0 5) (by simp) with h1795 | h1795
            · rcases p0_3 (m.d 0 6) (by simp) with h1796 | h1796
              · linarith only [h1796, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1798 | h1798
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1799 | h1799
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1800 | h1800
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1801 | h1801
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1802 | h1802
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1803 | h1803
                          · linarith only [h1793, h1799, h1803, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1793, h1803, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1793, h1798, h1799, h1802, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1793, h1798, h1799, h1801, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1790, h1800, hlam]
                  · linarith only [h1790, h1798, h1799, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1790, h1798, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1811 | h1811
              · linarith only [h1811, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1813 | h1813
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1814 | h1814
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1815 | h1815
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1816 | h1816
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1817 | h1817
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1818 | h1818
                          · linarith only [h1793, h1814, h1818, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1793, h1818, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1793, h1813, h1814, h1817, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1793, h1813, h1814, h1816, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1790, h1815, hlam]
                  · linarith only [h1790, h1813, h1814, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1790, h1813, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1794, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1827 | h1827
          · rcases p0_3 (m.d 0 5) (by simp) with h1828 | h1828
            · rcases p0_3 (m.d 0 6) (by simp) with h1829 | h1829
              · linarith only [h1829, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1831 | h1831
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1832 | h1832
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1833 | h1833
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1834 | h1834
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1835 | h1835
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1836 | h1836
                          · linarith only [h1833, h1836, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1793, h1836, hlam]
                        · linarith only [h1835, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1831, h1833, h1834, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1790, h1833, hlam]
                  · linarith only [h1790, h1831, h1832, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1790, h1831, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1844 | h1844
              · linarith only [h1844, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1846 | h1846
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1847 | h1847
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1848 | h1848
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1849 | h1849
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1850 | h1850
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1851 | h1851
                          · linarith only [h1848, h1851, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1793, h1851, hlam]
                        · linarith only [h1850, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h1846, h1848, h1849, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1790, h1848, hlam]
                  · linarith only [h1790, h1846, h1847, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1790, h1846, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1827, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1860 | h1860
      · linarith only [h1860, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1862 | h1862
        · rcases p0_3 (m.d 0 4) (by simp) with h1863 | h1863
          · rcases p0_3 (m.d 0 5) (by simp) with h1864 | h1864
            · rcases p0_3 (m.d 0 6) (by simp) with h1865 | h1865
              · linarith only [h1790, h1865, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1867 | h1867
                · linarith only [h1790, h1867, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1869 | h1869
                  · linarith only [h1862, h1867, h1869, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1862, h1867, h1869, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1872 | h1872
              · linarith only [h1790, h1872, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1874 | h1874
                · linarith only [h1790, h1874, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1876 | h1876
                  · linarith only [h1862, h1874, h1876, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1862, h1874, h1876, hc01, hc13, hlam, hphi, p0_1]
          · linarith only [h1863, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1880 | h1880
          · rcases p0_3 (m.d 0 5) (by simp) with h1881 | h1881
            · rcases p0_3 (m.d 0 6) (by simp) with h1882 | h1882
              · linarith only [h1790, h1882, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1884 | h1884
                · linarith only [h1790, h1884, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1886 | h1886
                  · linarith only [h1884, h1886, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1888 | h1888
                    · linarith only [h1884, h1888, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1884, h1888, hc01, hc14, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1891 | h1891
              · linarith only [h1790, h1891, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1893 | h1893
                · linarith only [h1790, h1893, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1895 | h1895
                  · linarith only [h1893, h1895, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1897 | h1897
                    · linarith only [h1893, h1897, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1893, h1897, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h1880, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1901 | h1901
    · rcases p0_3 (m.d 0 2) (by simp) with h1902 | h1902
      · rcases p0_3 (m.d 0 3) (by simp) with h1903 | h1903
        · linarith only [h1903, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1905 | h1905
          · rcases p0_3 (m.d 0 5) (by simp) with h1906 | h1906
            · rcases p0_3 (m.d 0 6) (by simp) with h1907 | h1907
              · linarith only [h1907, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1909 | h1909
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1910 | h1910
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1911 | h1911
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1912 | h1912
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1913 | h1913
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1914 | h1914
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1915 | h1915
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1916 | h1916
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1917 | h1917
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1918 | h1918
                                  · linarith only [h1918, hlam, p0_0]
                                  · linarith only [h1910, h1918, hc13, hc34, hlam, hphi, p0_1]
                                · linarith only [h1910, h1915, h1917, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1910, h1915, h1916, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1902, h1915, hlam]
                          · linarith only [h1902, h1910, h1914, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1910, h1911, h1913, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1910, h1911, h1912, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1901, h1911, hlam]
                  · linarith only [h1901, h1910, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1901, h1909, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1930 | h1930
              · linarith only [h1930, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1932 | h1932
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1933 | h1933
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1934 | h1934
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1935 | h1935
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1936 | h1936
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1937 | h1937
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1938 | h1938
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1939 | h1939
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1940 | h1940
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1941 | h1941
                                  · linarith only [h1941, hlam, p0_0]
                                  · linarith only [h1933, h1941, hc13, hc34, hlam, hphi, p0_1]
                                · linarith only [h1933, h1938, h1940, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1933, h1938, h1939, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1902, h1938, hlam]
                          · linarith only [h1902, h1933, h1937, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1933, h1934, h1936, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1933, h1934, h1935, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1901, h1934, hlam]
                  · linarith only [h1901, h1933, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1901, h1932, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1905, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1954 | h1954
        · linarith only [h1954, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1956 | h1956
          · rcases p0_3 (m.d 0 5) (by simp) with h1957 | h1957
            · rcases p0_3 (m.d 0 6) (by simp) with h1958 | h1958
              · linarith only [h1902, h1958, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1960 | h1960
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1961 | h1961
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1962 | h1962
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1963 | h1963
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1964 | h1964
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1965 | h1965
                          · linarith only [h1902, h1965, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1967 | h1967
                            · linarith only [h1962, h1965, h1967, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1965, h1967, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h1902, h1960, h1962, h1964, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1902, h1960, h1962, h1963, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1901, h1962, hlam]
                  · linarith only [h1901, h1902, h1960, h1961, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1901, h1902, h1960, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1975 | h1975
              · linarith only [h1902, h1975, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1977 | h1977
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1978 | h1978
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1979 | h1979
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1980 | h1980
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1981 | h1981
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1982 | h1982
                          · linarith only [h1902, h1982, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1984 | h1984
                            · linarith only [h1979, h1982, h1984, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1982, h1984, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h1902, h1977, h1979, h1981, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1902, h1977, h1979, h1980, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1901, h1979, hlam]
                  · linarith only [h1901, h1902, h1977, h1978, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1901, h1902, h1977, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1956, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1993 | h1993
      · rcases p0_3 (m.d 0 3) (by simp) with h1994 | h1994
        · linarith only [h1994, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1996 | h1996
          · rcases p0_3 (m.d 0 5) (by simp) with h1997 | h1997
            · rcases p0_3 (m.d 0 6) (by simp) with h1998 | h1998
              · linarith only [h1901, h1998, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2000 | h2000
                · linarith only [h1901, h1993, h2000, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1901, h1993, h2000, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2003 | h2003
              · linarith only [h1901, h2003, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2005 | h2005
                · linarith only [h1901, h1993, h2005, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1901, h1993, h2005, hc01, hc12, hlam, hphi, p0_1]
          · linarith only [h1996, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2009 | h2009
        · linarith only [h2009, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2011 | h2011
          · rcases p0_3 (m.d 0 5) (by simp) with h2012 | h2012
            · rcases p0_3 (m.d 0 6) (by simp) with h2013 | h2013
              · linarith only [h1901, h2013, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2015 | h2015
                · linarith only [h1901, h2015, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2017 | h2017
                  · linarith only [h1901, h2017, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2019 | h2019
                    · linarith only [h1993, h2015, h2019, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1993, h2015, h2019, hc01, hc14, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2022 | h2022
              · linarith only [h1993, h2022, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2024 | h2024
                · linarith only [h1901, h2024, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2026 | h2026
                  · linarith only [h1901, h2026, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2028 | h2028
                    · linarith only [h1993, h2024, h2028, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1993, h2024, h2028, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h2011, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2033 | h2033
    · rcases p0_3 (m.d 0 2) (by simp) with h2034 | h2034
      · rcases p0_3 (m.d 0 3) (by simp) with h2035 | h2035
        · rcases p0_3 (m.d 0 4) (by simp) with h2036 | h2036
          · rcases p0_3 (m.d 0 5) (by simp) with h2037 | h2037
            · linarith only [h2037, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2039 | h2039
              · linarith only [h2039, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2041 | h2041
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2042 | h2042
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2043 | h2043
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2044 | h2044
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2045 | h2045
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2046 | h2046
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2047 | h2047
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2048 | h2048
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2049 | h2049
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2050 | h2050
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2051 | h2051
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2052 | h2052
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2053 | h2053
                                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2054 | h2054
                                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2055 | h2055
                                            · linarith only [h2041, h2046, h2050, h2055, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                                            · linarith only [h2039, h2055, hlam]
                                          · linarith only [h2054, hc05, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, p0_1]
                                        · linarith only [h2053, hlam, p0_0]
                                      · linarith only [h2044, h2050, h2052, hc15, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                    · linarith only [h2044, h2050, h2051, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                  · linarith only [h2035, h2050, hlam]
                                · linarith only [h2049, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h2044, h2047, h2048, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                            · linarith only [h2034, h2047, hlam]
                          · linarith only [h2034, h2044, h2046, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                        · linarith only [h2043, h2044, h2045, hc15, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h2043, h2044, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h2033, h2043, hlam]
                  · linarith only [h2033, h2042, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h2033, h2041, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · linarith only [h2036, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2073 | h2073
          · rcases p0_3 (m.d 0 5) (by simp) with h2074 | h2074
            · linarith only [h2074, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2076 | h2076
              · linarith only [h2035, h2076, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2078 | h2078
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2079 | h2079
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2080 | h2080
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2081 | h2081
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2082 | h2082
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2083 | h2083
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2084 | h2084
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2085 | h2085
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2086 | h2086
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2087 | h2087
                                  · linarith only [h2035, h2078, h2084, h2087, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2035, h2087, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h2035, h2083, h2084, h2086, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2035, h2083, h2084, h2085, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2034, h2084, hlam]
                          · linarith only [h2034, h2035, h2083, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2035, h2079, h2080, h2082, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2035, h2079, h2080, h2081, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2033, h2080, hlam]
                  · linarith only [h2033, h2035, h2079, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2033, h2035, h2078, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h2073, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2100 | h2100
        · rcases p0_3 (m.d 0 4) (by simp) with h2101 | h2101
          · rcases p0_3 (m.d 0 5) (by simp) with h2102 | h2102
            · linarith only [h2102, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2104 | h2104
              · linarith only [h2034, h2104, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2106 | h2106
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2107 | h2107
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2108 | h2108
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2109 | h2109
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2110 | h2110
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2111 | h2111
                          · linarith only [h2034, h2100, h2107, h2111, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2034, h2100, h2111, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2034, h2100, h2106, h2107, h2110, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2034, h2100, h2106, h2107, h2109, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2033, h2108, hlam]
                  · linarith only [h2033, h2034, h2106, h2107, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2033, h2034, h2106, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h2101, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2120 | h2120
          · rcases p0_3 (m.d 0 5) (by simp) with h2121 | h2121
            · linarith only [h2121, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2123 | h2123
              · linarith only [h2034, h2123, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2125 | h2125
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2126 | h2126
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2127 | h2127
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2128 | h2128
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2129 | h2129
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2130 | h2130
                          · linarith only [h2034, h2127, h2130, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2132 | h2132
                            · linarith only [h2100, h2127, h2130, h2132, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2100, h2130, h2132, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h2034, h2125, h2127, h2129, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2034, h2125, h2127, h2128, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2033, h2127, hlam]
                  · linarith only [h2033, h2034, h2125, h2126, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2033, h2034, h2125, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h2120, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2141 | h2141
      · rcases p0_3 (m.d 0 3) (by simp) with h2142 | h2142
        · rcases p0_3 (m.d 0 4) (by simp) with h2143 | h2143
          · rcases p0_3 (m.d 0 5) (by simp) with h2144 | h2144
            · linarith only [h2144, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2146 | h2146
              · linarith only [h2033, h2146, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2148 | h2148
                · linarith only [h2033, h2141, h2148, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2033, h2141, h2148, hc01, hc12, hlam, hphi, p0_1]
          · linarith only [h2143, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2152 | h2152
          · rcases p0_3 (m.d 0 5) (by simp) with h2153 | h2153
            · linarith only [h2153, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2155 | h2155
              · linarith only [h2033, h2155, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2157 | h2157
                · linarith only [h2033, h2141, h2157, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2033, h2141, h2157, hc01, hc12, hlam, hphi, p0_1]
          · linarith only [h2152, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2161 | h2161
        · rcases p0_3 (m.d 0 4) (by simp) with h2162 | h2162
          · rcases p0_3 (m.d 0 5) (by simp) with h2163 | h2163
            · linarith only [h2163, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2165 | h2165
              · linarith only [h2033, h2165, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2167 | h2167
                · linarith only [h2033, h2161, h2167, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2169 | h2169
                  · linarith only [h2141, h2161, h2167, h2169, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2141, h2161, h2167, h2169, hc01, hc13, hlam, hphi, p0_1]
          · linarith only [h2162, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2173 | h2173
          · rcases p0_3 (m.d 0 5) (by simp) with h2174 | h2174
            · linarith only [h2174, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2176 | h2176
              · linarith only [h2141, h2176, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2178 | h2178
                · linarith only [h2033, h2178, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2180 | h2180
                  · linarith only [h2141, h2178, h2180, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2182 | h2182
                    · linarith only [h2141, h2178, h2182, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2141, h2178, h2182, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h2173, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2186 | h2186
    · rcases p0_3 (m.d 0 2) (by simp) with h2187 | h2187
      · rcases p0_3 (m.d 0 3) (by simp) with h2188 | h2188
        · rcases p0_3 (m.d 0 4) (by simp) with h2189 | h2189
          · rcases p0_3 (m.d 0 5) (by simp) with h2190 | h2190
            · rcases p0_3 (m.d 0 6) (by simp) with h2191 | h2191
              · linarith only [h2191, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2193 | h2193
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2194 | h2194
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2195 | h2195
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2196 | h2196
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2197 | h2197
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2198 | h2198
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2199 | h2199
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2200 | h2200
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2201 | h2201
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2202 | h2202
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2203 | h2203
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2204 | h2204
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2205 | h2205
                                        · linarith only [h2190, h2205, hlam]
                                        · linarith only [h2205, hc06, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                                      · linarith only [h2204, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2201, h2202, h2203, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                                  · linarith only [h2188, h2202, hlam]
                                · linarith only [h2201, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h2197, h2199, h2200, hc16, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                            · linarith only [h2187, h2199, hlam]
                          · linarith only [h2187, h2197, h2198, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                        · linarith only [h2197, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h2195, h2196, hc06, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                    · linarith only [h2186, h2195, hlam]
                  · linarith only [h2186, h2194, hc06, hc13, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                · linarith only [h2186, h2193, hc06, hc12, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2220 | h2220
              · linarith only [h2220, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2222 | h2222
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2223 | h2223
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2224 | h2224
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2225 | h2225
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2226 | h2226
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2227 | h2227
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2228 | h2228
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2229 | h2229
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2230 | h2230
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2231 | h2231
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2232 | h2232
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2233 | h2233
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2234 | h2234
                                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2235 | h2235
                                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2236 | h2236
                                            · linarith only [h2190, h2236, hlam]
                                            · linarith only [h2225, h2236, hc15, hlam, hphi, ht56, u6elo5]
                                          · linarith only [h2235, hlam, p0_0]
                                        · linarith only [h2234, hc06, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                                      · linarith only [h2190, h2225, h2231, h2233, hc15, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                    · linarith only [h2190, h2225, h2231, h2232, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                  · linarith only [h2188, h2231, hlam]
                                · linarith only [h2230, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h2190, h2225, h2228, h2229, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                            · linarith only [h2187, h2228, hlam]
                          · linarith only [h2187, h2190, h2225, h2227, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                        · linarith only [h2190, h2224, h2225, h2226, hc15, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h2190, h2224, h2225, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h2186, h2224, hlam]
                  · linarith only [h2186, h2190, h2223, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h2186, h2190, h2222, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · linarith only [h2189, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2254 | h2254
          · rcases p0_3 (m.d 0 5) (by simp) with h2255 | h2255
            · rcases p0_3 (m.d 0 6) (by simp) with h2256 | h2256
              · linarith only [h2256, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2258 | h2258
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2259 | h2259
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2260 | h2260
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2261 | h2261
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2262 | h2262
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2263 | h2263
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2264 | h2264
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2265 | h2265
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2266 | h2266
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2267 | h2267
                                  · linarith only [h2188, h2258, h2264, h2267, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2188, h2267, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h2188, h2263, h2264, h2266, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2188, h2263, h2264, h2265, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2187, h2264, hlam]
                          · linarith only [h2187, h2188, h2263, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2262, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h2188, h2259, h2260, h2261, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2186, h2260, hlam]
                  · linarith only [h2186, h2188, h2259, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2188, h2258, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2279 | h2279
              · linarith only [h2279, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2281 | h2281
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2282 | h2282
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2283 | h2283
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2284 | h2284
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2285 | h2285
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2286 | h2286
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2287 | h2287
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2288 | h2288
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2289 | h2289
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2290 | h2290
                                  · linarith only [h2188, h2281, h2287, h2290, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2188, h2290, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h2188, h2282, h2287, h2289, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2188, h2282, h2287, h2288, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2187, h2287, hlam]
                          · linarith only [h2187, h2188, h2282, h2286, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2188, h2282, h2283, h2285, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2188, h2282, h2283, h2284, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2186, h2283, hlam]
                  · linarith only [h2186, h2188, h2282, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2188, h2281, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h2254, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2303 | h2303
        · rcases p0_3 (m.d 0 4) (by simp) with h2304 | h2304
          · rcases p0_3 (m.d 0 5) (by simp) with h2305 | h2305
            · rcases p0_3 (m.d 0 6) (by simp) with h2306 | h2306
              · linarith only [h2306, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2308 | h2308
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2309 | h2309
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2310 | h2310
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2311 | h2311
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2312 | h2312
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2313 | h2313
                          · linarith only [h2187, h2303, h2309, h2313, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2187, h2303, h2313, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2187, h2303, h2308, h2309, h2312, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2187, h2303, h2308, h2309, h2311, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2186, h2310, hlam]
                  · linarith only [h2186, h2187, h2308, h2309, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2187, h2308, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2321 | h2321
              · linarith only [h2321, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2323 | h2323
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2324 | h2324
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2325 | h2325
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2326 | h2326
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2327 | h2327
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2328 | h2328
                          · linarith only [h2187, h2303, h2324, h2328, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2187, h2303, h2328, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2187, h2303, h2323, h2324, h2327, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2187, h2303, h2323, h2324, h2326, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2186, h2325, hlam]
                  · linarith only [h2186, h2187, h2323, h2324, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2187, h2323, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h2304, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2337 | h2337
          · rcases p0_3 (m.d 0 5) (by simp) with h2338 | h2338
            · rcases p0_3 (m.d 0 6) (by simp) with h2339 | h2339
              · linarith only [h2339, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2341 | h2341
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2342 | h2342
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2343 | h2343
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2344 | h2344
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2345 | h2345
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2346 | h2346
                          · linarith only [h2187, h2343, h2346, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2348 | h2348
                            · linarith only [h2303, h2343, h2346, h2348, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2303, h2346, h2348, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h2187, h2341, h2343, h2345, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2187, h2341, h2343, h2344, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2186, h2343, hlam]
                  · linarith only [h2186, h2187, h2341, h2342, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2187, h2341, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2356 | h2356
              · linarith only [h2356, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2358 | h2358
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2359 | h2359
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2360 | h2360
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2361 | h2361
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2362 | h2362
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2363 | h2363
                          · linarith only [h2187, h2360, h2363, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2365 | h2365
                            · linarith only [h2303, h2360, h2363, h2365, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2303, h2363, h2365, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h2187, h2358, h2360, h2362, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2187, h2358, h2360, h2361, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2186, h2360, hlam]
                  · linarith only [h2186, h2187, h2358, h2359, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2187, h2358, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h2337, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2374 | h2374
      · rcases p0_3 (m.d 0 3) (by simp) with h2375 | h2375
        · rcases p0_3 (m.d 0 4) (by simp) with h2376 | h2376
          · rcases p0_3 (m.d 0 5) (by simp) with h2377 | h2377
            · rcases p0_3 (m.d 0 6) (by simp) with h2378 | h2378
              · linarith only [h2378, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2380 | h2380
                · linarith only [h2186, h2374, h2380, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2374, h2380, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2383 | h2383
              · linarith only [h2383, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2385 | h2385
                · linarith only [h2186, h2374, h2385, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2374, h2385, hc01, hc12, hlam, hphi, p0_1]
          · linarith only [h2376, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2389 | h2389
          · rcases p0_3 (m.d 0 5) (by simp) with h2390 | h2390
            · rcases p0_3 (m.d 0 6) (by simp) with h2391 | h2391
              · linarith only [h2391, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2393 | h2393
                · linarith only [h2186, h2374, h2393, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2374, h2393, hc01, hc12, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2396 | h2396
              · linarith only [h2396, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2398 | h2398
                · linarith only [h2186, h2374, h2398, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2186, h2374, h2398, hc01, hc12, hlam, hphi, p0_1]
          · linarith only [h2389, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2402 | h2402
        · rcases p0_3 (m.d 0 4) (by simp) with h2403 | h2403
          · rcases p0_3 (m.d 0 5) (by simp) with h2404 | h2404
            · rcases p0_3 (m.d 0 6) (by simp) with h2405 | h2405
              · linarith only [h2405, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2407 | h2407
                · linarith only [h2186, h2402, h2407, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2409 | h2409
                  · linarith only [h2374, h2402, h2407, h2409, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2374, h2402, h2407, h2409, hc01, hc13, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2412 | h2412
              · linarith only [h2412, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2414 | h2414
                · linarith only [h2186, h2402, h2414, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2416 | h2416
                  · linarith only [h2374, h2402, h2414, h2416, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2374, h2402, h2414, h2416, hc01, hc13, hlam, hphi, p0_1]
          · linarith only [h2403, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2420 | h2420
          · rcases p0_3 (m.d 0 5) (by simp) with h2421 | h2421
            · rcases p0_3 (m.d 0 6) (by simp) with h2422 | h2422
              · linarith only [h2422, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2424 | h2424
                · linarith only [h2186, h2424, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2426 | h2426
                  · linarith only [h2374, h2424, h2426, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2428 | h2428
                    · linarith only [h2374, h2424, h2428, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2374, h2424, h2428, hc01, hc14, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h2431 | h2431
              · linarith only [h2431, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2433 | h2433
                · linarith only [h2186, h2433, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2435 | h2435
                  · linarith only [h2374, h2433, h2435, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2437 | h2437
                    · linarith only [h2374, h2433, h2437, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2374, h2433, h2437, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h2420, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2441 | h2441
    · linarith only [h2441, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2443 | h2443
      · rcases p0_3 (m.d 0 3) (by simp) with h2444 | h2444
        · rcases p0_3 (m.d 0 4) (by simp) with h2445 | h2445
          · rcases p0_3 (m.d 0 5) (by simp) with h2446 | h2446
            · rcases p0_3 (m.d 0 6) (by simp) with h2447 | h2447
              · linarith only [h2447, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2449 | h2449
                · linarith only [h2443, h2449, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2443, h2449, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h2446, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2453 | h2453
            · rcases p0_3 (m.d 0 6) (by simp) with h2454 | h2454
              · linarith only [h2454, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2456 | h2456
                · linarith only [h2443, h2456, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2443, h2456, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h2453, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2460 | h2460
          · rcases p0_3 (m.d 0 5) (by simp) with h2461 | h2461
            · rcases p0_3 (m.d 0 6) (by simp) with h2462 | h2462
              · linarith only [h2462, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2464 | h2464
                · linarith only [h2443, h2464, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2443, h2464, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h2461, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2468 | h2468
            · rcases p0_3 (m.d 0 6) (by simp) with h2469 | h2469
              · linarith only [h2469, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2471 | h2471
                · linarith only [h2443, h2471, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2443, h2471, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h2468, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2475 | h2475
        · rcases p0_3 (m.d 0 4) (by simp) with h2476 | h2476
          · rcases p0_3 (m.d 0 5) (by simp) with h2477 | h2477
            · rcases p0_3 (m.d 0 6) (by simp) with h2478 | h2478
              · linarith only [h2478, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2480 | h2480
                · linarith only [h2475, h2480, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2443, h2480, hlam]
            · linarith only [h2477, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2484 | h2484
            · rcases p0_3 (m.d 0 6) (by simp) with h2485 | h2485
              · linarith only [h2485, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2487 | h2487
                · linarith only [h2487, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2443, h2487, hlam]
            · linarith only [h2484, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2491 | h2491
          · rcases p0_3 (m.d 0 5) (by simp) with h2492 | h2492
            · rcases p0_3 (m.d 0 6) (by simp) with h2493 | h2493
              · linarith only [h2493, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2495 | h2495
                · linarith only [h2491, h2495, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2443, h2495, hlam]
            · linarith only [h2492, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2499 | h2499
            · rcases p0_3 (m.d 0 6) (by simp) with h2500 | h2500
              · linarith only [h2500, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2502 | h2502
                · linarith only [h2502, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2443, h2502, hlam]
            · linarith only [h2499, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2506 | h2506
    · rcases p0_3 (m.d 0 2) (by simp) with h2507 | h2507
      · linarith only [h2507, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2509 | h2509
        · rcases p0_3 (m.d 0 4) (by simp) with h2510 | h2510
          · rcases p0_3 (m.d 0 5) (by simp) with h2511 | h2511
            · rcases p0_3 (m.d 0 6) (by simp) with h2512 | h2512
              · linarith only [h2512, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2514 | h2514
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2515 | h2515
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2516 | h2516
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2517 | h2517
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2518 | h2518
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2519 | h2519
                          · linarith only [h2509, h2515, h2519, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2509, h2514, h2519, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h2509, h2514, h2515, h2518, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2506, h2517, hlam]
                    · linarith only [h2509, h2514, h2515, h2516, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2506, h2514, h2515, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2506, h2514, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2511, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2528 | h2528
            · rcases p0_3 (m.d 0 6) (by simp) with h2529 | h2529
              · linarith only [h2529, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2531 | h2531
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2532 | h2532
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2533 | h2533
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2534 | h2534
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2535 | h2535
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2536 | h2536
                          · linarith only [h2509, h2532, h2536, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2509, h2536, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2509, h2531, h2532, h2535, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2506, h2534, hlam]
                    · linarith only [h2509, h2531, h2532, h2533, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2506, h2531, h2532, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2506, h2531, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2528, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2545 | h2545
          · rcases p0_3 (m.d 0 5) (by simp) with h2546 | h2546
            · rcases p0_3 (m.d 0 6) (by simp) with h2547 | h2547
              · linarith only [h2547, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2549 | h2549
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2550 | h2550
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2551 | h2551
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2552 | h2552
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2553 | h2553
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2554 | h2554
                          · linarith only [h2545, h2551, h2554, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2509, h2554, hlam]
                        · linarith only [h2553, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h2506, h2552, hlam]
                    · linarith only [h2506, h2549, h2551, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2506, h2549, h2550, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2506, h2549, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2546, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2563 | h2563
            · rcases p0_3 (m.d 0 6) (by simp) with h2564 | h2564
              · linarith only [h2564, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2566 | h2566
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2567 | h2567
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2568 | h2568
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2569 | h2569
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2570 | h2570
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2571 | h2571
                          · linarith only [h2569, h2571, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2509, h2571, hlam]
                        · linarith only [h2570, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
                      · linarith only [h2506, h2569, hlam]
                    · linarith only [h2506, h2566, h2568, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2506, h2566, h2567, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2506, h2566, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2563, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2580 | h2580
      · linarith only [h2580, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2582 | h2582
        · rcases p0_3 (m.d 0 4) (by simp) with h2583 | h2583
          · rcases p0_3 (m.d 0 5) (by simp) with h2584 | h2584
            · rcases p0_3 (m.d 0 6) (by simp) with h2585 | h2585
              · linarith only [h2506, h2585, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2587 | h2587
                · linarith only [h2506, h2587, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2589 | h2589
                  · linarith only [h2582, h2587, h2589, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2582, h2587, h2589, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h2584, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2593 | h2593
            · rcases p0_3 (m.d 0 6) (by simp) with h2594 | h2594
              · linarith only [h2506, h2594, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2596 | h2596
                · linarith only [h2506, h2596, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2598 | h2598
                  · linarith only [h2582, h2596, h2598, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2582, h2596, h2598, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h2593, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2602 | h2602
          · rcases p0_3 (m.d 0 5) (by simp) with h2603 | h2603
            · rcases p0_3 (m.d 0 6) (by simp) with h2604 | h2604
              · linarith only [h2506, h2604, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2606 | h2606
                · linarith only [h2506, h2606, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2608 | h2608
                  · linarith only [h2602, h2606, h2608, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2610 | h2610
                    · linarith only [h2602, h2606, h2610, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2602, h2606, h2610, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h2603, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2614 | h2614
            · rcases p0_3 (m.d 0 6) (by simp) with h2615 | h2615
              · linarith only [h2615, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2617 | h2617
                · linarith only [h2506, h2617, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2619 | h2619
                  · linarith only [h2617, h2619, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2621 | h2621
                    · linarith only [h2617, h2621, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2623 | h2623
                      · linarith only [h2617, h2623, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h2617, h2623, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h2614, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2627 | h2627
    · rcases p0_3 (m.d 0 2) (by simp) with h2628 | h2628
      · rcases p0_3 (m.d 0 3) (by simp) with h2629 | h2629
        · linarith only [h2629, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2631 | h2631
          · rcases p0_3 (m.d 0 5) (by simp) with h2632 | h2632
            · rcases p0_3 (m.d 0 6) (by simp) with h2633 | h2633
              · linarith only [h2633, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2635 | h2635
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2636 | h2636
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2637 | h2637
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2638 | h2638
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2639 | h2639
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2640 | h2640
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2641 | h2641
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2642 | h2642
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2643 | h2643
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2644 | h2644
                                  · linarith only [h2631, h2635, h2641, h2644, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2631, h2644, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h2631, h2636, h2641, h2643, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2628, h2642, hlam]
                            · linarith only [h2628, h2636, h2641, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2628, h2636, h2640, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2636, h2638, h2639, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2627, h2638, hlam]
                    · linarith only [h2627, h2636, h2637, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2628, h2635, h2636, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2627, h2635, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2632, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2657 | h2657
            · rcases p0_3 (m.d 0 6) (by simp) with h2658 | h2658
              · linarith only [h2658, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2660 | h2660
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2661 | h2661
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2662 | h2662
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2663 | h2663
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2664 | h2664
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2665 | h2665
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2666 | h2666
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2667 | h2667
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2668 | h2668
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2669 | h2669
                                  · linarith only [h2660, h2667, h2669, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2631, h2669, hlam]
                                · linarith only [h2668, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h2628, h2667, hlam]
                            · linarith only [h2628, h2665, h2666, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2628, h2665, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2661, h2663, h2664, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2627, h2663, hlam]
                    · linarith only [h2627, h2661, h2662, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2628, h2660, h2661, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2627, h2660, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2657, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2682 | h2682
        · linarith only [h2682, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2684 | h2684
          · rcases p0_3 (m.d 0 5) (by simp) with h2685 | h2685
            · rcases p0_3 (m.d 0 6) (by simp) with h2686 | h2686
              · linarith only [h2628, h2686, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2688 | h2688
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2689 | h2689
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2690 | h2690
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2691 | h2691
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2692 | h2692
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2693 | h2693
                          · linarith only [h2628, h2693, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2695 | h2695
                            · linarith only [h2684, h2690, h2693, h2695, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2684, h2693, h2695, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h2628, h2684, h2688, h2690, h2692, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2627, h2691, hlam]
                    · linarith only [h2627, h2628, h2688, h2690, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2627, h2628, h2688, h2689, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2627, h2628, h2688, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2685, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2704 | h2704
            · rcases p0_3 (m.d 0 6) (by simp) with h2705 | h2705
              · linarith only [h2628, h2705, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2707 | h2707
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2708 | h2708
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2709 | h2709
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2710 | h2710
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2711 | h2711
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2712 | h2712
                          · linarith only [h2628, h2712, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2714 | h2714
                            · linarith only [h2710, h2712, h2714, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2716 | h2716
                              · linarith only [h2710, h2712, h2716, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · linarith only [h2712, h2716, hc02, hc25, hlam, hphi, p0_1]
                        · linarith only [h2628, h2707, h2710, h2711, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2627, h2710, hlam]
                    · linarith only [h2627, h2628, h2707, h2709, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2627, h2628, h2707, h2708, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2627, h2628, h2707, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2704, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2725 | h2725
      · rcases p0_3 (m.d 0 3) (by simp) with h2726 | h2726
        · linarith only [h2726, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2728 | h2728
          · rcases p0_3 (m.d 0 5) (by simp) with h2729 | h2729
            · rcases p0_3 (m.d 0 6) (by simp) with h2730 | h2730
              · linarith only [h2627, h2730, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2732 | h2732
                · linarith only [h2627, h2725, h2732, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2627, h2725, h2732, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h2729, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2736 | h2736
            · rcases p0_3 (m.d 0 6) (by simp) with h2737 | h2737
              · linarith only [h2627, h2737, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2739 | h2739
                · linarith only [h2627, h2725, h2739, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2627, h2725, h2739, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h2736, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2743 | h2743
        · linarith only [h2743, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2745 | h2745
          · rcases p0_3 (m.d 0 5) (by simp) with h2746 | h2746
            · rcases p0_3 (m.d 0 6) (by simp) with h2747 | h2747
              · linarith only [h2627, h2747, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2749 | h2749
                · linarith only [h2627, h2745, h2749, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2751 | h2751
                  · linarith only [h2627, h2751, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2753 | h2753
                    · linarith only [h2725, h2745, h2749, h2753, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2725, h2745, h2749, h2753, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h2746, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2757 | h2757
            · rcases p0_3 (m.d 0 6) (by simp) with h2758 | h2758
              · linarith only [h2725, h2758, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2760 | h2760
                · linarith only [h2627, h2760, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2762 | h2762
                  · linarith only [h2627, h2762, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2764 | h2764
                    · linarith only [h2725, h2760, h2764, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2766 | h2766
                      · linarith only [h2725, h2760, h2766, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h2725, h2760, h2766, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h2757, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2770 | h2770
    · rcases p0_3 (m.d 0 2) (by simp) with h2771 | h2771
      · rcases p0_3 (m.d 0 3) (by simp) with h2772 | h2772
        · rcases p0_3 (m.d 0 4) (by simp) with h2773 | h2773
          · linarith only [h2773, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2775 | h2775
            · rcases p0_3 (m.d 0 6) (by simp) with h2776 | h2776
              · linarith only [h2776, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2778 | h2778
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2779 | h2779
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2780 | h2780
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2781 | h2781
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2782 | h2782
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2783 | h2783
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2784 | h2784
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2785 | h2785
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2786 | h2786
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2787 | h2787
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2788 | h2788
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2789 | h2789
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2790 | h2790
                                        · linarith only [h2790, hlam, p0_0]
                                        · linarith only [h2780, h2790, hc14, hc45, hlam, hphi, p0_1]
                                      · linarith only [h2780, h2788, h2789, hc14, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                    · linarith only [h2772, h2788, hlam]
                                  · linarith only [h2772, h2780, h2787, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h2780, h2785, h2786, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2771, h2785, hlam]
                            · linarith only [h2771, h2780, h2784, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2771, h2780, h2783, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2780, h2781, h2782, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2770, h2781, hlam]
                    · linarith only [h2770, h2780, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2771, h2778, h2779, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h2770, h2778, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · linarith only [h2775, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2806 | h2806
          · linarith only [h2806, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2808 | h2808
            · rcases p0_3 (m.d 0 6) (by simp) with h2809 | h2809
              · linarith only [h2772, h2809, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2811 | h2811
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2812 | h2812
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2813 | h2813
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2814 | h2814
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2815 | h2815
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2816 | h2816
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2817 | h2817
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2818 | h2818
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2819 | h2819
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2820 | h2820
                                  · linarith only [h2772, h2820, hlam]
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2822 | h2822
                                    · linarith only [h2811, h2818, h2820, h2822, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                    · linarith only [h2820, h2822, hc03, hc35, hlam, hphi, p0_1]
                                · linarith only [h2818, h2819, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2771, h2818, hlam]
                            · linarith only [h2771, h2772, h2812, h2817, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2771, h2772, h2812, h2816, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2772, h2812, h2814, h2815, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2770, h2814, hlam]
                    · linarith only [h2770, h2772, h2812, h2813, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2771, h2772, h2811, h2812, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2770, h2772, h2811, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2808, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2835 | h2835
        · rcases p0_3 (m.d 0 4) (by simp) with h2836 | h2836
          · linarith only [h2836, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2838 | h2838
            · rcases p0_3 (m.d 0 6) (by simp) with h2839 | h2839
              · linarith only [h2771, h2839, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2841 | h2841
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2842 | h2842
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2843 | h2843
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2844 | h2844
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2845 | h2845
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2846 | h2846
                          · linarith only [h2771, h2835, h2842, h2846, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2771, h2835, h2841, h2846, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h2771, h2835, h2841, h2842, h2845, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2770, h2844, hlam]
                    · linarith only [h2771, h2835, h2841, h2842, h2843, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2770, h2771, h2841, h2842, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2770, h2771, h2841, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2838, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2855 | h2855
          · linarith only [h2855, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2857 | h2857
            · rcases p0_3 (m.d 0 6) (by simp) with h2858 | h2858
              · linarith only [h2771, h2858, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2860 | h2860
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2861 | h2861
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2862 | h2862
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2863 | h2863
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2864 | h2864
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2865 | h2865
                          · linarith only [h2771, h2863, h2865, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2867 | h2867
                            · linarith only [h2771, h2867, hlam]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2869 | h2869
                              · linarith only [h2835, h2863, h2865, h2869, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · linarith only [h2835, h2865, h2869, hc02, hc25, hlam, hphi, p0_1]
                        · linarith only [h2771, h2860, h2863, h2864, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2770, h2863, hlam]
                    · linarith only [h2770, h2771, h2860, h2862, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2770, h2771, h2860, h2861, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2770, h2771, h2860, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h2857, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2878 | h2878
      · rcases p0_3 (m.d 0 3) (by simp) with h2879 | h2879
        · rcases p0_3 (m.d 0 4) (by simp) with h2880 | h2880
          · linarith only [h2880, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2882 | h2882
            · rcases p0_3 (m.d 0 6) (by simp) with h2883 | h2883
              · linarith only [h2770, h2883, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2885 | h2885
                · linarith only [h2770, h2878, h2885, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2770, h2878, h2885, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h2882, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2889 | h2889
          · linarith only [h2889, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2891 | h2891
            · rcases p0_3 (m.d 0 6) (by simp) with h2892 | h2892
              · linarith only [h2770, h2892, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2894 | h2894
                · linarith only [h2770, h2878, h2894, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2770, h2878, h2894, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h2891, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2898 | h2898
        · rcases p0_3 (m.d 0 4) (by simp) with h2899 | h2899
          · linarith only [h2899, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2901 | h2901
            · rcases p0_3 (m.d 0 6) (by simp) with h2902 | h2902
              · linarith only [h2770, h2902, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2904 | h2904
                · linarith only [h2770, h2898, h2904, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2906 | h2906
                  · linarith only [h2878, h2898, h2904, h2906, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2878, h2898, h2904, h2906, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h2901, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2910 | h2910
          · linarith only [h2910, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2912 | h2912
            · rcases p0_3 (m.d 0 6) (by simp) with h2913 | h2913
              · linarith only [h2878, h2913, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2915 | h2915
                · linarith only [h2770, h2915, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2917 | h2917
                  · linarith only [h2878, h2915, h2917, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2919 | h2919
                    · linarith only [h2770, h2919, hlam]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2921 | h2921
                      · linarith only [h2878, h2915, h2921, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h2878, h2915, h2921, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h2912, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2926 | h2926
    · rcases p0_3 (m.d 0 2) (by simp) with h2927 | h2927
      · rcases p0_3 (m.d 0 3) (by simp) with h2928 | h2928
        · rcases p0_3 (m.d 0 4) (by simp) with h2929 | h2929
          · rcases p0_3 (m.d 0 5) (by simp) with h2930 | h2930
            · rcases p0_3 (m.d 0 6) (by simp) with h2931 | h2931
              · linarith only [h2931, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2933 | h2933
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2934 | h2934
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2935 | h2935
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2936 | h2936
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2937 | h2937
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2938 | h2938
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2939 | h2939
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2940 | h2940
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2941 | h2941
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2942 | h2942
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2943 | h2943
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2944 | h2944
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2945 | h2945
                                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2946 | h2946
                                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2947 | h2947
                                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2948 | h2948
                                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2949 | h2949
                                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2950 | h2950
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2951 | h2951
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2952 | h2952
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2953 | h2953
                                                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2954 | h2954
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2955 | h2955
                                                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2956 | h2956
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2957 | h2957
                                                                · linarith only [h2933, h2948, h2952, h2957, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                                                · linarith only [h2933, h2948, h2952, h2955, h2957, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                              · linarith only [h2956, hc24, hlam, hphi, ht45, ht56, u6elo4]
                                                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2961 | h2961
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2962 | h2962
                                                                · linarith only [h2933, h2938, h2942, h2955, h2961, h2962, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                                · rcases m.htr 3 4 6 (by decide) (by decide) with h2964 | h2964
                                                                  · linarith only [h2933, h2948, h2953, h2962, h2964, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                                  · linarith only [h2955, h2961, h2964, hc34, hc45, hlam, hphi]
                                                              · linarith only [h2933, h2938, h2942, h2945, h2946, h2961, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h2954, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                                        · linarith only [h2933, h2948, h2951, h2952, h2953, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2970 | h2970
                                                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2971 | h2971
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2972 | h2972
                                                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2973 | h2973
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2974 | h2974
                                                                · rcases m.htr 3 4 6 (by decide) (by decide) with h2975 | h2975
                                                                  · rcases m.htr 3 5 6 (by decide) (by decide) with h2976 | h2976
                                                                    · linarith only [h2933, h2938, h2942, h2952, h2970, h2976, hc01, hc56, hlam, hphi, ht0b, ht6b]
                                                                    · linarith only [h2976, hc35, hlam, hphi, ht56, u6elo5]
                                                                  · linarith only [h2952, h2975, hc23, hlam, hphi, ht34, ht45, ht56, u6elo4]
                                                                · linarith only [h2933, h2938, h2942, h2945, h2952, h2970, h2974, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                              · linarith only [h2973, hc24, hlam, hphi, ht45, ht56, u6elo4]
                                                            · linarith only [h2952, h2970, h2972, hlam]
                                                          · linarith only [h2970, h2971, hc35, hlam, hphi, ht56, u6elo3]
                                                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2984 | h2984
                                                          · linarith only [h2933, h2948, h2951, h2970, h2984, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                          · linarith only [h2984, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2987 | h2987
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2988 | h2988
                                                        · linarith only [h2933, h2948, h2951, h2988, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2990 | h2990
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2991 | h2991
                                                            · linarith only [h2987, h2988, h2991, hlam]
                                                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2993 | h2993
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2994 | h2994
                                                                · linarith only [h2948, h2951, h2987, h2991, h2994, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                                                · rcases m.htr 3 4 6 (by decide) (by decide) with h2996 | h2996
                                                                  · linarith only [h2933, h2938, h2942, h2945, h2948, h2951, h2987, h2994, h2996, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                                  · linarith only [h2996, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                              · linarith only [h2933, h2938, h2942, h2945, h2946, h2993, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h2990, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3001 | h3001
                                                        · linarith only [h2951, h2987, h3001, hc13, hc34, hlam, hphi]
                                                        · rcases m.htr 2 3 6 (by decide) (by decide) with h3003 | h3003
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3004 | h3004
                                                            · rcases m.htr 2 4 6 (by decide) (by decide) with h3005 | h3005
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3006 | h3006
                                                                · rcases m.htr 3 4 6 (by decide) (by decide) with h3007 | h3007
                                                                  · rcases m.htr 3 5 6 (by decide) (by decide) with h3008 | h3008
                                                                    · rcases m.htr 4 5 6 (by decide) (by decide) with h3009 | h3009
                                                                      · linarith only [h2933, h2949, h3004, h3009, hc01, hc56, hlam, hphi, ht0b, ht6b]
                                                                      · linarith only [h3009, hc45, hlam, hphi, ht56, u6elo5]
                                                                    · linarith only [h2933, h2938, h2942, h2945, h2947, h2948, h2951, h3003, h3007, h3008, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                                  · linarith only [h3007, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                                · linarith only [h2933, h2938, h2942, h2945, h2987, h3003, h3006, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                              · linarith only [h3005, hc24, hlam, hphi, ht45, ht56, u6elo4]
                                                            · rcases m.htr 2 4 6 (by decide) (by decide) with h3016 | h3016
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3017 | h3017
                                                                · linarith only [h2933, h2938, h2942, h2987, h3003, h3004, h3017, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                                · linarith only [h2933, h2938, h2942, h2945, h2987, h3003, h3017, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                              · linarith only [h2987, h3003, h3016, hc36, hlam, hphi, u6elo4]
                                                          · linarith only [h3003, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                                  · linarith only [h2950, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3023 | h3023
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3024 | h3024
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3025 | h3025
                                                      · linarith only [h2933, h2939, h2948, h2949, h3025, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3027 | h3027
                                                        · linarith only [h2933, h2938, h2942, h2948, h2949, h3025, h3027, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                        · linarith only [h2933, h2938, h2942, h2948, h2949, h3024, h3025, h3027, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3030 | h3030
                                                      · linarith only [h2933, h2939, h2948, h2949, h3030, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3032 | h3032
                                                        · linarith only [h2933, h2938, h2942, h2948, h2949, h3024, h3030, h3032, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                        · rcases m.htr 2 3 6 (by decide) (by decide) with h3034 | h3034
                                                          · linarith only [h2933, h2938, h2942, h2948, h2949, h3030, h3034, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                          · linarith only [h3034, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                                  · linarith only [h3023, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3038 | h3038
                                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3039 | h3039
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3040 | h3040
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3041 | h3041
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3042 | h3042
                                                        · rcases m.htr 2 3 6 (by decide) (by decide) with h3043 | h3043
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3044 | h3044
                                                            · linarith only [h2933, h2938, h2948, h3038, h3044, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                                            · rcases m.htr 2 4 6 (by decide) (by decide) with h3046 | h3046
                                                              · linarith only [h2933, h2938, h2948, h3038, h3046, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                              · linarith only [h3046, hc24, hlam, hphi, ht45, ht56, u6elo4]
                                                          · linarith only [h2948, h3043, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                                        · linarith only [h2936, h2948, h3038, h3040, h3041, h3042, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                      · linarith only [h2933, h2938, h2942, h2948, h3038, h3041, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3052 | h3052
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3053 | h3053
                                                        · linarith only [h2933, h2938, h2948, h3038, h3040, h3052, h3053, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                        · linarith only [h2933, h2938, h2943, h2948, h3038, h3052, h3053, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                      · linarith only [h2933, h2938, h2942, h2948, h3038, h3052, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                  · linarith only [h3038, h3039, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3058 | h3058
                                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3059 | h3059
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3060 | h3060
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3061 | h3061
                                                        · rcases m.htr 2 3 6 (by decide) (by decide) with h3062 | h3062
                                                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3063 | h3063
                                                            · rcases m.htr 2 4 6 (by decide) (by decide) with h3064 | h3064
                                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3065 | h3065
                                                                · rcases m.htr 3 4 6 (by decide) (by decide) with h3066 | h3066
                                                                  · rcases m.htr 3 5 6 (by decide) (by decide) with h3067 | h3067
                                                                    · rcases m.htr 4 5 6 (by decide) (by decide) with h3068 | h3068
                                                                      · linarith only [h2933, h2938, h3060, h3065, h3068, hc01, hc56, hlam, hphi, ht0b, ht6b]
                                                                      · linarith only [h3068, hc45, hlam, hphi, ht56, u6elo5]
                                                                    · linarith only [h2933, h2938, h2942, h2945, h2947, h3067, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                                  · linarith only [h3066, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                                · rcases m.htr 3 4 6 (by decide) (by decide) with h3073 | h3073
                                                                  · linarith only [h2933, h2938, h3060, h3063, h3065, h3073, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                                  · linarith only [h3073, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                              · linarith only [h2933, h2938, h2942, h2945, h2946, h3038, h3064, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                                            · linarith only [h2933, h2938, h2942, h2945, h3038, h3058, h3062, h3063, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                          · linarith only [h2948, h3062, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                                        · linarith only [h2933, h2938, h2943, h3038, h3058, h3060, h3061, hc01, hc26, hlam, hphi, ht0b, ht6b]
                                                      · linarith only [h2933, h2938, h2942, h2948, h3058, h3060, hc01, hc26, hlam, hphi, ht0b, ht6b]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3081 | h3081
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3082 | h3082
                                                        · linarith only [h2933, h2938, h2948, h3058, h3059, h3082, hc01, hc26, hlam, hphi, ht0b, ht6b]
                                                        · linarith only [h2933, h2938, h2943, h2948, h3058, h3082, hc01, hc26, hlam, hphi, ht0b, ht6b]
                                                      · linarith only [h2933, h2938, h2942, h2948, h3058, h3081, hc01, hc26, hlam, hphi, ht0b, ht6b]
                                                  · linarith only [h3058, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                            · linarith only [h2947, hlam, p0_0]
                                          · linarith only [h2945, h2946, hc06, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                                        · linarith only [h2929, h2945, hlam]
                                      · linarith only [h2937, h2943, h2944, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                                    · linarith only [h2928, h2943, hlam]
                                  · linarith only [h2928, h2937, h2942, hc16, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                                · linarith only [h2937, h2940, h2941, hc16, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                              · linarith only [h2927, h2940, hlam]
                            · linarith only [h2927, h2937, h2939, hc16, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                          · linarith only [h2927, h2937, h2938, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                        · linarith only [h2936, h2937, hc06, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                      · linarith only [h2926, h2936, hlam]
                    · linarith only [h2926, h2935, hc06, hc14, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                  · linarith only [h2927, h2933, h2934, hc06, hc13, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                · linarith only [h2926, h2933, hc06, hc12, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · linarith only [h2930, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3103 | h3103
            · rcases p0_3 (m.d 0 6) (by simp) with h3104 | h3104
              · linarith only [h3104, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3106 | h3106
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3107 | h3107
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3108 | h3108
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3109 | h3109
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3110 | h3110
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3111 | h3111
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h3112 | h3112
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h3113 | h3113
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h3114 | h3114
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h3115 | h3115
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3116 | h3116
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3117 | h3117
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3118 | h3118
                                        · linarith only [h2929, h3106, h3111, h3116, h3118, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                        · linarith only [h2929, h3118, hc04, hc45, hlam, hphi, p0_1]
                                      · linarith only [h2929, h3112, h3116, h3117, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                    · linarith only [h2928, h3116, hlam]
                                  · linarith only [h2928, h2929, h3112, h3115, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h2929, h3112, h3113, h3114, hc24, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2927, h3113, hlam]
                            · linarith only [h2927, h2929, h3112, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2927, h2929, h3108, h3111, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2929, h3108, h3109, h3110, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2926, h3109, hlam]
                    · linarith only [h2926, h2929, h3108, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2927, h2929, h3106, h3107, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h2929, h3106, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · linarith only [h3103, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h3134 | h3134
          · rcases p0_3 (m.d 0 5) (by simp) with h3135 | h3135
            · rcases p0_3 (m.d 0 6) (by simp) with h3136 | h3136
              · linarith only [h3136, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3138 | h3138
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3139 | h3139
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3140 | h3140
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3141 | h3141
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3142 | h3142
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3143 | h3143
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h3144 | h3144
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h3145 | h3145
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h3146 | h3146
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h3147 | h3147
                                  · linarith only [h2928, h3134, h3138, h3144, h3147, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2928, h3134, h3147, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h2928, h3134, h3143, h3144, h3146, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2927, h3145, hlam]
                            · linarith only [h2927, h2928, h3143, h3144, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2927, h2928, h3143, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2928, h3139, h3141, h3142, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2926, h3141, hlam]
                    · linarith only [h2926, h2928, h3139, h3140, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2927, h2928, h3138, h3139, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h2928, h3138, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h3135, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3160 | h3160
            · rcases p0_3 (m.d 0 6) (by simp) with h3161 | h3161
              · linarith only [h3161, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3163 | h3163
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3164 | h3164
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3165 | h3165
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3166 | h3166
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3167 | h3167
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3168 | h3168
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h3169 | h3169
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h3170 | h3170
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h3171 | h3171
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h3172 | h3172
                                  · linarith only [h2928, h3163, h3170, h3172, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3174 | h3174
                                    · linarith only [h3134, h3163, h3170, h3172, h3174, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                    · linarith only [h3134, h3172, h3174, hc03, hc35, hlam, hphi, p0_1]
                                · linarith only [h3134, h3170, h3171, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2927, h3170, hlam]
                            · linarith only [h2927, h2928, h3168, h3169, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2927, h2928, h3164, h3168, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2928, h3164, h3166, h3167, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2926, h3166, hlam]
                    · linarith only [h2926, h2928, h3164, h3165, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2927, h2928, h3163, h3164, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h2928, h3163, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h3160, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h3187 | h3187
        · rcases p0_3 (m.d 0 4) (by simp) with h3188 | h3188
          · rcases p0_3 (m.d 0 5) (by simp) with h3189 | h3189
            · rcases p0_3 (m.d 0 6) (by simp) with h3190 | h3190
              · linarith only [h3190, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3192 | h3192
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3193 | h3193
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3194 | h3194
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3195 | h3195
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3196 | h3196
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3197 | h3197
                          · linarith only [h2927, h3187, h3193, h3197, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2927, h3187, h3197, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2927, h3187, h3192, h3193, h3196, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2926, h3195, hlam]
                    · linarith only [h2927, h3187, h3192, h3193, h3194, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2926, h2927, h3192, h3193, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h2927, h3192, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h3189, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3206 | h3206
            · rcases p0_3 (m.d 0 6) (by simp) with h3207 | h3207
              · linarith only [h3207, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3209 | h3209
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3210 | h3210
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3211 | h3211
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3212 | h3212
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3213 | h3213
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3214 | h3214
                          · linarith only [h2927, h3187, h3210, h3214, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2927, h3187, h3214, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2927, h3187, h3209, h3210, h3213, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2926, h3212, hlam]
                    · linarith only [h2927, h3187, h3209, h3210, h3211, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2926, h2927, h3209, h3210, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h2927, h3209, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h3206, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h3223 | h3223
          · rcases p0_3 (m.d 0 5) (by simp) with h3224 | h3224
            · rcases p0_3 (m.d 0 6) (by simp) with h3225 | h3225
              · linarith only [h3225, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3227 | h3227
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3228 | h3228
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3229 | h3229
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3230 | h3230
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3231 | h3231
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3232 | h3232
                          · linarith only [h2927, h3223, h3229, h3232, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h3234 | h3234
                            · linarith only [h3187, h3223, h3229, h3232, h3234, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h3187, h3223, h3232, h3234, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h2927, h3223, h3227, h3229, h3231, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2926, h3230, hlam]
                    · linarith only [h2926, h2927, h3227, h3229, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2926, h2927, h3227, h3228, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h2927, h3227, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h3224, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3243 | h3243
            · rcases p0_3 (m.d 0 6) (by simp) with h3244 | h3244
              · linarith only [h3244, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3246 | h3246
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3247 | h3247
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3248 | h3248
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3249 | h3249
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3250 | h3250
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3251 | h3251
                          · linarith only [h2927, h3249, h3251, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h3253 | h3253
                            · linarith only [h3187, h3249, h3251, h3253, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h3255 | h3255
                              · linarith only [h3187, h3249, h3251, h3255, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · linarith only [h3187, h3251, h3255, hc02, hc25, hlam, hphi, p0_1]
                        · linarith only [h2927, h3246, h3249, h3250, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2926, h3249, hlam]
                    · linarith only [h2926, h2927, h3246, h3248, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2926, h2927, h3246, h3247, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h2927, h3246, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h3243, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h3264 | h3264
      · rcases p0_3 (m.d 0 3) (by simp) with h3265 | h3265
        · rcases p0_3 (m.d 0 4) (by simp) with h3266 | h3266
          · rcases p0_3 (m.d 0 5) (by simp) with h3267 | h3267
            · rcases p0_3 (m.d 0 6) (by simp) with h3268 | h3268
              · linarith only [h3268, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3270 | h3270
                · linarith only [h2926, h3264, h3270, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h3264, h3270, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h3267, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3274 | h3274
            · rcases p0_3 (m.d 0 6) (by simp) with h3275 | h3275
              · linarith only [h3275, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3277 | h3277
                · linarith only [h2926, h3264, h3277, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h3264, h3277, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h3274, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h3281 | h3281
          · rcases p0_3 (m.d 0 5) (by simp) with h3282 | h3282
            · rcases p0_3 (m.d 0 6) (by simp) with h3283 | h3283
              · linarith only [h3283, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3285 | h3285
                · linarith only [h2926, h3264, h3285, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h3264, h3285, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h3282, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3289 | h3289
            · rcases p0_3 (m.d 0 6) (by simp) with h3290 | h3290
              · linarith only [h3290, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3292 | h3292
                · linarith only [h2926, h3264, h3292, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2926, h3264, h3292, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h3289, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h3296 | h3296
        · rcases p0_3 (m.d 0 4) (by simp) with h3297 | h3297
          · rcases p0_3 (m.d 0 5) (by simp) with h3298 | h3298
            · rcases p0_3 (m.d 0 6) (by simp) with h3299 | h3299
              · linarith only [h3299, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3301 | h3301
                · linarith only [h2926, h3296, h3301, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3303 | h3303
                  · linarith only [h3264, h3296, h3301, h3303, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h3264, h3296, h3301, h3303, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h3298, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3307 | h3307
            · rcases p0_3 (m.d 0 6) (by simp) with h3308 | h3308
              · linarith only [h3308, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3310 | h3310
                · linarith only [h2926, h3296, h3310, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3312 | h3312
                  · linarith only [h3264, h3296, h3310, h3312, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h3264, h3296, h3310, h3312, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h3307, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h3316 | h3316
          · rcases p0_3 (m.d 0 5) (by simp) with h3317 | h3317
            · rcases p0_3 (m.d 0 6) (by simp) with h3318 | h3318
              · linarith only [h3318, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3320 | h3320
                · linarith only [h2926, h3316, h3320, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3322 | h3322
                  · linarith only [h3264, h3316, h3320, h3322, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3324 | h3324
                    · linarith only [h3264, h3316, h3320, h3324, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h3264, h3316, h3320, h3324, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h3317, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3328 | h3328
            · rcases p0_3 (m.d 0 6) (by simp) with h3329 | h3329
              · linarith only [h3329, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3331 | h3331
                · linarith only [h2926, h3331, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3333 | h3333
                  · linarith only [h3264, h3331, h3333, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3335 | h3335
                    · linarith only [h3264, h3331, h3335, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3337 | h3337
                      · linarith only [h3264, h3331, h3337, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h3264, h3331, h3337, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h3328, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

set_option maxHeartbeats 6622000 in
theorem n8l_sBT8_H_R_H_I (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_I m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
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
  have hc06 := m.hcor 0 6 (by decide)
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
  have h6bigk := hb6.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 6) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 6) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 6) (by simp) with h7 | h7
            · rcases p0_3 (m.d 5 6) (by simp) with h8 | h8
              · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
                · rcases m.htr 0 1 6 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h11 | h11
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h12 | h12
                      · linarith only [h12, h5, hlam]
                      · linarith only [h12, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h11, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h10, hlam, p0_0]
                · linarith only [h9, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h18 | h18
                · rcases m.htr 0 1 6 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h21 | h21
                      · linarith only [h21, h5, hlam]
                      · linarith only [h20, h21, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h20, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h19, hlam, p0_0]
                · linarith only [h18, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h27 | h27
              · rcases m.htr 0 1 2 (by decide) (by decide) with h28 | h28
                · rcases m.htr 0 1 6 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h31 | h31
                      · linarith only [h31, h5, hlam]
                      · linarith only [h30, h31, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h30, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h29, hlam, p0_0]
                · linarith only [h28, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h37 | h37
                · rcases m.htr 0 1 6 (by decide) (by decide) with h38 | h38
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h39 | h39
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h40 | h40
                      · linarith only [h40, h5, hlam]
                      · linarith only [h39, h40, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h39, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h38, hlam, p0_0]
                · linarith only [h37, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h46 | h46
            · rcases p0_3 (m.d 5 6) (by simp) with h47 | h47
              · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
                · rcases m.htr 0 1 6 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h50 | h50
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h51 | h51
                      · linarith only [h5, h51, hlam]
                      · linarith only [h50, h51, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h50, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h49, hlam, p0_0]
                · linarith only [h48, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h57 | h57
                · rcases m.htr 0 1 6 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h60 | h60
                      · linarith only [h5, h60, hlam]
                      · linarith only [h59, h60, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h59, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h58, hlam, p0_0]
                · linarith only [h57, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h66 | h66
              · rcases m.htr 0 1 2 (by decide) (by decide) with h67 | h67
                · rcases m.htr 0 1 6 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h69 | h69
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h70 | h70
                      · linarith only [h5, h70, hlam]
                      · linarith only [h69, h70, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h69, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h68, hlam, p0_0]
                · linarith only [h67, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 1 6 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h79 | h79
                      · linarith only [h5, h79, hlam]
                      · linarith only [h78, h79, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h78, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h77, hlam, p0_0]
                · linarith only [h76, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h85 | h85
          · rcases p0_3 (m.d 4 6) (by simp) with h86 | h86
            · rcases p0_3 (m.d 5 6) (by simp) with h87 | h87
              · rcases m.htr 0 1 2 (by decide) (by decide) with h88 | h88
                · rcases m.htr 0 1 6 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h92 | h92
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h93 | h93
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h94 | h94
                            · linarith only [h85, h94, hlam]
                            · linarith only [h92, h94, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h92, h93, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h92, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h5, h91, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h90, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h89, hlam, p0_0]
                · linarith only [h88, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
                · rcases m.htr 0 1 6 (by decide) (by decide) with h104 | h104
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h108 | h108
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h109 | h109
                            · linarith only [h109, h85, hlam]
                            · linarith only [h107, h109, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h107, h108, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h107, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h106, h5, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h105, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h104, hlam, p0_0]
                · linarith only [h103, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h118 | h118
              · rcases m.htr 0 1 2 (by decide) (by decide) with h119 | h119
                · rcases m.htr 0 1 6 (by decide) (by decide) with h120 | h120
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h121 | h121
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h122 | h122
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h125 | h125
                            · linarith only [h125, h85, hlam]
                            · linarith only [h123, h125, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h123, h124, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h123, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h118, h122, h5, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h121, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h120, hlam, p0_0]
                · linarith only [h119, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
                · rcases m.htr 0 1 6 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h138 | h138
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h139 | h139
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h140 | h140
                            · linarith only [h140, h85, hlam]
                            · linarith only [h138, h140, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h138, h139, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h138, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h137, h5, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h136, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h135, hlam, p0_0]
                · linarith only [h134, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h149 | h149
            · rcases p0_3 (m.d 5 6) (by simp) with h150 | h150
              · rcases m.htr 0 1 2 (by decide) (by decide) with h151 | h151
                · rcases m.htr 0 1 6 (by decide) (by decide) with h152 | h152
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h153 | h153
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h154 | h154
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h155 | h155
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h156 | h156
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h157 | h157
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h158 | h158
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h159 | h159
                                · linarith only [h149, h159, hlam]
                                · linarith only [h158, h159, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                              · linarith only [h158, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h150, h157, h85, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                          · linarith only [h155, h156, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h155, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h150, h154, h5, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h153, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h152, hlam, p0_0]
                · linarith only [h151, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h170 | h170
                · rcases m.htr 0 1 6 (by decide) (by decide) with h171 | h171
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h172 | h172
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h173 | h173
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h174 | h174
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h175 | h175
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h176 | h176
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h178 | h178
                                · linarith only [h149, h178, hlam]
                                · linarith only [h177, h178, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                              · linarith only [h177, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h176, h85, hc03, hc06, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h174, h175, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h174, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h149, h173, h5, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h172, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h171, hlam, p0_0]
                · linarith only [h170, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h189 | h189
              · rcases m.htr 0 1 2 (by decide) (by decide) with h190 | h190
                · rcases m.htr 0 1 6 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h192 | h192
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h193 | h193
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h194 | h194
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h195 | h195
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h196 | h196
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h197 | h197
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h198 | h198
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h199 | h199
                                  · linarith only [h189, h199, hlam]
                                  · linarith only [h199, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4]
                                · linarith only [h149, h198, hc04, hc06, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h197, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h189, h196, h85, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                          · linarith only [h194, h195, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h194, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h189, h193, h5, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h192, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h191, hlam, p0_0]
                · linarith only [h190, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h211 | h211
                · rcases m.htr 0 1 6 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h214 | h214
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h215 | h215
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h216 | h216
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h217 | h217
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h218 | h218
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h219 | h219
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h220 | h220
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h224 | h224
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h225 | h225
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h226 | h226
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h227 | h227
                                                · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h230 | h230
                                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h231 | h231
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h232 | h232
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
                                                            · linarith only [h211, h221, h228, h233, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                                            · linarith only [h211, h221, h228, h231, h233, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                          · linarith only [h211, h213, h215, h218, h220, h226, h232, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h237 | h237
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                                                            · linarith only [h211, h213, h215, h231, h237, h238, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h240 | h240
                                                              · linarith only [h211, h221, h228, h240, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                              · linarith only [h231, h237, h240, hc34, hc45, hlam, hphi]
                                                          · linarith only [h211, h213, h215, h218, h220, h226, h237, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h211, h213, h215, h218, h220, h225, h230, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h245 | h245
                                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                                                        · linarith only [h228, h229, h246, hlam]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h248 | h248
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h249 | h249
                                                            · linarith only [h228, h229, h246, h249, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h251 | h251
                                                              · linarith only [h211, h213, h215, h218, h228, h229, h249, h251, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                              · linarith only [h211, h213, h215, h218, h220, h226, h251, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h211, h213, h215, h218, h220, h226, h248, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h211, h213, h215, h218, h220, h225, h228, h245, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h257 | h257
                                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h259 | h259
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h261 | h261
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h262 | h262
                                                                · linarith only [h211, h213, h215, h228, h256, h262, hc01, hc56, hlam, hphi, ht0b, ht6b]
                                                                · linarith only [h211, h213, h215, h218, h220, h227, h262, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                              · linarith only [h211, h213, h215, h218, h220, h226, h228, h261, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                            · linarith only [h211, h213, h215, h218, h228, h257, h260, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                          · linarith only [h211, h213, h215, h218, h220, h226, h259, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h228, h256, h258, hlam]
                                                      · linarith only [h211, h213, h215, h218, h220, h225, h257, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h270 | h270
                                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h271 | h271
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h272 | h272
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h273 | h273
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h274 | h274
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h275 | h275
                                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h276 | h276
                                                                  · linarith only [h211, h222, h271, h276, hc01, hc56, hlam, hphi, ht0b, ht6b]
                                                                  · linarith only [h211, h213, h215, h218, h220, h227, h276, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                                · linarith only [h211, h213, h215, h218, h220, h227, h256, h270, h274, h275, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                              · linarith only [h211, h213, h215, h218, h220, h226, h256, h273, h274, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                            · linarith only [h211, h213, h215, h218, h228, h270, h273, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                          · linarith only [h211, h213, h215, h218, h220, h226, h272, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h283 | h283
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                                                            · linarith only [h211, h213, h215, h228, h270, h271, h284, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                            · linarith only [h211, h213, h215, h218, h228, h270, h284, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                          · linarith only [h211, h213, h215, h218, h220, h226, h228, h270, h283, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                                      · linarith only [h211, h213, h215, h218, h220, h225, h270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                · linarith only [h189, h227, hlam]
                                              · linarith only [h149, h226, hlam]
                                            · linarith only [h225, h85, hlam]
                                          · linarith only [h224, h5, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h293 | h293
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h294 | h294
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h295 | h295
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h296 | h296
                                                · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h298 | h298
                                                    · linarith only [h221, h223, h298, hlam]
                                                    · linarith only [h211, h213, h216, h221, h223, h297, h298, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h301 | h301
                                                    · linarith only [h222, h223, h297, h301, hlam]
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h303 | h303
                                                      · linarith only [h211, h213, h216, h222, h223, h297, h301, h303, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                      · linarith only [h211, h213, h215, h218, h220, h294, h303, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                · linarith only [h189, h296, hlam]
                                              · linarith only [h149, h295, hlam]
                                            · linarith only [h294, h85, hlam]
                                          · linarith only [h293, h5, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h310 | h310
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h311 | h311
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h312 | h312
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h313 | h313
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h314 | h314
                                                · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                                                  · linarith only [h221, h222, h315, hlam]
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h317 | h317
                                                    · linarith only [h211, h213, h215, h221, h222, h315, h317, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h319 | h319
                                                      · linarith only [h211, h213, h215, h222, h310, h315, h317, h319, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                      · linarith only [h211, h213, h215, h218, h220, h312, h319, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                · linarith only [h189, h314, hlam]
                                              · linarith only [h149, h313, hlam]
                                            · linarith only [h312, h85, hlam]
                                          · linarith only [h311, h5, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h326 | h326
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h327 | h327
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h328 | h328
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h329 | h329
                                                · rcases m.htr 2 3 4 (by decide) (by decide) with h330 | h330
                                                  · linarith only [h221, h222, h330, hlam]
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h332 | h332
                                                    · linarith only [h211, h213, h215, h221, h222, h330, h332, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h334 | h334
                                                      · linarith only [h211, h213, h215, h221, h222, h330, h334, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                      · linarith only [h211, h213, h215, h218, h220, h327, h334, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                · linarith only [h189, h329, hlam]
                                              · linarith only [h149, h328, hlam]
                                            · linarith only [h327, h85, hlam]
                                          · linarith only [h326, h5, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h343 | h343
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h344 | h344
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h345 | h345
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h346 | h346
                                                · rcases m.htr 2 3 4 (by decide) (by decide) with h347 | h347
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h348 | h348
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h349 | h349
                                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
                                                        · linarith only [h211, h213, h221, h341, h350, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h352 | h352
                                                          · linarith only [h211, h213, h221, h342, h350, h352, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                          · linarith only [h211, h213, h215, h218, h220, h345, h352, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h211, h213, h215, h218, h220, h221, h344, h349, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h211, h213, h216, h221, h341, h347, h348, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                  · linarith only [h211, h213, h215, h221, h341, h347, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                · linarith only [h189, h346, hlam]
                                              · linarith only [h149, h345, hlam]
                                            · linarith only [h344, h85, hlam]
                                          · linarith only [h343, h5, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h362 | h362
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h363 | h363
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h364 | h364
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h365 | h365
                                                · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h367 | h367
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h368 | h368
                                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h369 | h369
                                                        · linarith only [h211, h213, h341, h342, h367, h369, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h371 | h371
                                                          · linarith only [h211, h213, h215, h218, h341, h342, h369, h371, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                          · linarith only [h211, h213, h215, h218, h220, h364, h371, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h211, h213, h215, h218, h220, h342, h363, h367, h368, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h211, h213, h216, h221, h341, h366, h367, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                  · linarith only [h211, h213, h215, h221, h341, h366, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                · linarith only [h189, h365, hlam]
                                              · linarith only [h149, h364, hlam]
                                            · linarith only [h363, h85, hlam]
                                          · linarith only [h362, h5, hlam]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h381 | h381
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h382 | h382
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h383 | h383
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h384 | h384
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h385 | h385
                                                · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h387 | h387
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h388 | h388
                                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h389 | h389
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h390 | h390
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h391 | h391
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h392 | h392
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h393 | h393
                                                                · linarith only [h211, h213, h341, h381, h386, h387, h393, hc01, hc56, hlam, hphi, ht0b, ht6b]
                                                                · linarith only [h211, h213, h215, h218, h220, h385, h393, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                              · linarith only [h211, h213, h215, h218, h220, h384, h392, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                            · linarith only [h211, h213, h341, h381, h386, h389, h391, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                          · linarith only [h211, h213, h215, h218, h220, h341, h384, h390, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h211, h213, h215, h218, h341, h381, h387, h389, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                      · linarith only [h211, h213, h215, h218, h220, h341, h381, h383, h386, h387, h388, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                    · linarith only [h211, h213, h216, h341, h381, h386, h387, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                                                  · linarith only [h211, h213, h215, h221, h381, h386, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                                                · linarith only [h189, h385, hlam]
                                              · linarith only [h149, h384, hlam]
                                            · linarith only [h383, h85, hlam]
                                          · linarith only [h382, h5, hlam]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h407 | h407
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h408 | h408
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h409 | h409
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h410 | h410
                                                · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h412 | h412
                                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h413 | h413
                                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h414 | h414
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h415 | h415
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h417 | h417
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h418 | h418
                                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h419 | h419
                                                                  · linarith only [h211, h213, h411, h416, h419, hc01, hc56, hlam, hphi, ht0b, ht6b]
                                                                  · linarith only [h211, h213, h215, h218, h220, h410, h419, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                                · linarith only [h211, h213, h215, h218, h220, h410, h418, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                              · linarith only [h211, h213, h215, h218, h220, h409, h417, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h424 | h424
                                                              · linarith only [h211, h213, h411, h414, h416, h424, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                              · linarith only [h211, h213, h215, h218, h220, h409, h424, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h211, h213, h215, h218, h220, h409, h415, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h211, h213, h215, h218, h341, h407, h414, hc01, hc26, hlam, hphi, ht0b, ht6b]
                                                      · linarith only [h211, h213, h215, h218, h220, h408, h413, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h211, h213, h216, h341, h407, h411, h412, hc01, hc26, hlam, hphi, ht0b, ht6b]
                                                  · linarith only [h211, h213, h215, h221, h407, h411, hc01, hc26, hlam, hphi, ht0b, ht6b]
                                                · linarith only [h189, h410, hlam]
                                              · linarith only [h149, h409, hlam]
                                            · linarith only [h408, h85, hlam]
                                          · linarith only [h407, h5, hlam]
                                  · linarith only [h220, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4]
                                · linarith only [h219, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                              · linarith only [h218, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h217, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h215, h216, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h215, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h214, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h213, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h212, hlam, p0_0]
                · linarith only [h211, hc12, hlam, hphi, ht01, u0ehi0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h447 | h447
    · rcases p0_3 (m.d 1 6) (by simp) with h448 | h448
      · rcases p0_3 (m.d 2 6) (by simp) with h449 | h449
        · linarith only [h449, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h451 | h451
          · rcases p0_3 (m.d 4 6) (by simp) with h452 | h452
            · rcases p0_3 (m.d 5 6) (by simp) with h453 | h453
              · rcases m.htr 0 1 2 (by decide) (by decide) with h454 | h454
                · rcases m.htr 0 1 6 (by decide) (by decide) with h455 | h455
                  · linarith only [h448, h455, hlam]
                  · linarith only [h454, h455, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h454, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h459 | h459
                · rcases m.htr 0 1 6 (by decide) (by decide) with h460 | h460
                  · linarith only [h448, h460, hlam]
                  · linarith only [h459, h460, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h459, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h464 | h464
              · rcases m.htr 0 1 2 (by decide) (by decide) with h465 | h465
                · rcases m.htr 0 1 6 (by decide) (by decide) with h466 | h466
                  · linarith only [h448, h466, hlam]
                  · linarith only [h465, h466, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h465, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h470 | h470
                · rcases m.htr 0 1 6 (by decide) (by decide) with h471 | h471
                  · linarith only [h448, h471, hlam]
                  · linarith only [h470, h471, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h470, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h475 | h475
            · rcases p0_3 (m.d 5 6) (by simp) with h476 | h476
              · rcases m.htr 0 1 2 (by decide) (by decide) with h477 | h477
                · rcases m.htr 0 1 6 (by decide) (by decide) with h478 | h478
                  · linarith only [h448, h478, hlam]
                  · linarith only [h477, h478, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h477, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h482 | h482
                · rcases m.htr 0 1 6 (by decide) (by decide) with h483 | h483
                  · linarith only [h448, h483, hlam]
                  · linarith only [h482, h483, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h482, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h487 | h487
              · rcases m.htr 0 1 2 (by decide) (by decide) with h488 | h488
                · rcases m.htr 0 1 6 (by decide) (by decide) with h489 | h489
                  · linarith only [h448, h489, hlam]
                  · linarith only [h488, h489, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h488, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h493 | h493
                · rcases m.htr 0 1 6 (by decide) (by decide) with h494 | h494
                  · linarith only [h448, h494, hlam]
                  · linarith only [h493, h494, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h493, hc12, hlam, hphi, ht01, u0ehi0]
      · rcases p0_3 (m.d 2 6) (by simp) with h498 | h498
        · linarith only [h498, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h500 | h500
          · rcases p0_3 (m.d 4 6) (by simp) with h501 | h501
            · rcases p0_3 (m.d 5 6) (by simp) with h502 | h502
              · rcases m.htr 0 1 2 (by decide) (by decide) with h503 | h503
                · rcases m.htr 0 1 6 (by decide) (by decide) with h504 | h504
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h505 | h505
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h506 | h506
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h507 | h507
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h508 | h508
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h509 | h509
                            · linarith only [h500, h509, hlam]
                            · linarith only [h507, h509, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h507, h508, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h507, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h506, hlam, p0_0]
                    · linarith only [h505, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h448, h503, h504, hc06, hlam, hphi, p0_1, u0ehi1]
                · linarith only [h503, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h518 | h518
                · rcases m.htr 0 1 6 (by decide) (by decide) with h519 | h519
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h520 | h520
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h521 | h521
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h522 | h522
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h523 | h523
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h524 | h524
                            · linarith only [h500, h524, hlam]
                            · linarith only [h522, h524, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h522, h523, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h522, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h521, hlam, p0_0]
                    · linarith only [h520, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h448, h518, h519, hc06, hlam, hphi, p0_1, u0ehi1]
                · linarith only [h518, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h533 | h533
              · rcases m.htr 0 1 2 (by decide) (by decide) with h534 | h534
                · rcases m.htr 0 1 6 (by decide) (by decide) with h535 | h535
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h536 | h536
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h537 | h537
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h538 | h538
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h539 | h539
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h540 | h540
                            · linarith only [h500, h540, hlam]
                            · linarith only [h538, h540, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h538, h539, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h538, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h537, hlam, p0_0]
                    · linarith only [h536, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h448, h533, h534, h535, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi1]
                · linarith only [h534, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h549 | h549
                · rcases m.htr 0 1 6 (by decide) (by decide) with h550 | h550
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h551 | h551
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h552 | h552
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h553 | h553
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h554 | h554
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h555 | h555
                            · linarith only [h500, h555, hlam]
                            · linarith only [h553, h555, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h553, h554, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h553, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h552, hlam, p0_0]
                    · linarith only [h551, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h448, h549, h550, hc06, hlam, hphi, p0_1, u0ehi1]
                · linarith only [h549, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h564 | h564
            · rcases p0_3 (m.d 5 6) (by simp) with h565 | h565
              · rcases m.htr 0 1 2 (by decide) (by decide) with h566 | h566
                · rcases m.htr 0 1 6 (by decide) (by decide) with h567 | h567
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h568 | h568
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h569 | h569
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h570 | h570
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h572 | h572
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h574 | h574
                                · linarith only [h564, h574, hlam]
                                · linarith only [h573, h574, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                              · linarith only [h573, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h500, h565, h572, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                          · linarith only [h570, h571, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h570, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h569, hlam, p0_0]
                    · linarith only [h568, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h448, h565, h567, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h566, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h585 | h585
                · rcases m.htr 0 1 6 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h587 | h587
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h588 | h588
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h589 | h589
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h590 | h590
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h591 | h591
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h592 | h592
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h593 | h593
                                · linarith only [h564, h593, hlam]
                                · linarith only [h592, h593, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                              · linarith only [h592, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h500, h591, hc03, hc06, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h589, h590, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h589, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h588, hlam, p0_0]
                    · linarith only [h587, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h448, h564, h586, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h585, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h604 | h604
              · rcases m.htr 0 1 2 (by decide) (by decide) with h605 | h605
                · rcases m.htr 0 1 6 (by decide) (by decide) with h606 | h606
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h607 | h607
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h608 | h608
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h609 | h609
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h610 | h610
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h611 | h611
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h612 | h612
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h613 | h613
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h614 | h614
                                  · linarith only [h604, h614, hlam]
                                  · linarith only [h614, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4]
                                · linarith only [h564, h613, hc04, hc06, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h612, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h500, h604, h611, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                          · linarith only [h609, h610, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h609, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h608, hlam, p0_0]
                    · linarith only [h607, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h448, h604, h605, h606, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi1]
                · linarith only [h605, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h626 | h626
                · rcases m.htr 0 1 6 (by decide) (by decide) with h627 | h627
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h628 | h628
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h629 | h629
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h630 | h630
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h631 | h631
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h632 | h632
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h633 | h633
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h634 | h634
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h635 | h635
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h636 | h636
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h637 | h637
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h638 | h638
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h639 | h639
                                          · linarith only [h448, h639, hlam]
                                          · linarith only [h626, h628, h630, h633, h635, h639, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h642 | h642
                                          · linarith only [h448, h642, hlam]
                                          · linarith only [h626, h628, h630, h633, h635, h636, h642, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h645 | h645
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h646 | h646
                                          · linarith only [h448, h646, hlam]
                                          · linarith only [h626, h628, h630, h633, h635, h636, h646, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h649 | h649
                                          · linarith only [h448, h649, hlam]
                                          · linarith only [h626, h628, h630, h633, h635, h636, h649, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h652 | h652
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h653 | h653
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h654 | h654
                                          · linarith only [h448, h654, hlam]
                                          · linarith only [h626, h628, h630, h633, h635, h654, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h657 | h657
                                          · linarith only [h448, h657, hlam]
                                          · linarith only [h626, h628, h630, h633, h635, h652, h657, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h661 | h661
                                          · linarith only [h448, h661, hlam]
                                          · linarith only [h626, h628, h630, h633, h635, h661, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h664 | h664
                                          · linarith only [h448, h664, hlam]
                                          · linarith only [h626, h628, h630, h633, h635, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h604, h635, hc05, hc06, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                · linarith only [h564, h626, h628, h632, h634, hc01, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h633, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h500, h632, hc03, hc06, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h630, h631, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h630, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h629, hlam, p0_0]
                    · linarith only [h628, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h627, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h626, hc12, hlam, hphi, ht01, u0ehi0]
    · linarith only [h447, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h678 | h678
    · rcases p0_3 (m.d 1 6) (by simp) with h679 | h679
      · rcases p0_3 (m.d 2 6) (by simp) with h680 | h680
        · rcases p0_3 (m.d 3 6) (by simp) with h681 | h681
          · linarith only [h681, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h683 | h683
            · rcases p0_3 (m.d 5 6) (by simp) with h684 | h684
              · rcases m.htr 0 1 2 (by decide) (by decide) with h685 | h685
                · rcases m.htr 0 1 6 (by decide) (by decide) with h686 | h686
                  · linarith only [h679, h686, hlam]
                  · linarith only [h685, h686, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h685, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h690 | h690
                · rcases m.htr 0 1 6 (by decide) (by decide) with h691 | h691
                  · linarith only [h679, h691, hlam]
                  · linarith only [h690, h691, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h690, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h695 | h695
              · rcases m.htr 0 1 2 (by decide) (by decide) with h696 | h696
                · rcases m.htr 0 1 6 (by decide) (by decide) with h697 | h697
                  · linarith only [h679, h697, hlam]
                  · linarith only [h696, h697, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h696, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h701 | h701
                · rcases m.htr 0 1 6 (by decide) (by decide) with h702 | h702
                  · linarith only [h679, h702, hlam]
                  · linarith only [h701, h702, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h701, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h706 | h706
          · linarith only [h706, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h708 | h708
            · rcases p0_3 (m.d 5 6) (by simp) with h709 | h709
              · rcases m.htr 0 1 2 (by decide) (by decide) with h710 | h710
                · rcases m.htr 0 1 6 (by decide) (by decide) with h711 | h711
                  · linarith only [h679, h711, hlam]
                  · linarith only [h710, h711, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h710, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h715 | h715
                · rcases m.htr 0 1 6 (by decide) (by decide) with h716 | h716
                  · linarith only [h679, h716, hlam]
                  · linarith only [h715, h716, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h715, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h720 | h720
              · rcases m.htr 0 1 2 (by decide) (by decide) with h721 | h721
                · rcases m.htr 0 1 6 (by decide) (by decide) with h722 | h722
                  · linarith only [h679, h722, hlam]
                  · linarith only [h721, h722, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h721, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h726 | h726
                · rcases m.htr 0 1 6 (by decide) (by decide) with h727 | h727
                  · linarith only [h679, h727, hlam]
                  · linarith only [h726, h727, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h726, hc12, hlam, hphi, ht01, u0ehi0]
      · rcases p0_3 (m.d 2 6) (by simp) with h731 | h731
        · rcases p0_3 (m.d 3 6) (by simp) with h732 | h732
          · linarith only [h732, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h734 | h734
            · rcases p0_3 (m.d 5 6) (by simp) with h735 | h735
              · rcases m.htr 0 1 2 (by decide) (by decide) with h736 | h736
                · rcases m.htr 0 1 6 (by decide) (by decide) with h737 | h737
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h738 | h738
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h739 | h739
                      · linarith only [h731, h739, hlam]
                      · linarith only [h738, h739, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h738, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h679, h737, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h736, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h745 | h745
                · rcases m.htr 0 1 6 (by decide) (by decide) with h746 | h746
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h747 | h747
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h748 | h748
                      · linarith only [h731, h748, hlam]
                      · linarith only [h747, h748, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h747, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h679, h746, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h745, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h754 | h754
              · rcases m.htr 0 1 2 (by decide) (by decide) with h755 | h755
                · rcases m.htr 0 1 6 (by decide) (by decide) with h756 | h756
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h757 | h757
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h758 | h758
                      · linarith only [h731, h758, hlam]
                      · linarith only [h757, h758, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h757, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h679, h754, h756, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h755, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h764 | h764
                · rcases m.htr 0 1 6 (by decide) (by decide) with h765 | h765
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h766 | h766
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h767 | h767
                      · linarith only [h731, h767, hlam]
                      · linarith only [h766, h767, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h766, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h679, h765, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h764, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h773 | h773
          · linarith only [h773, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h775 | h775
            · rcases p0_3 (m.d 5 6) (by simp) with h776 | h776
              · rcases m.htr 0 1 2 (by decide) (by decide) with h777 | h777
                · rcases m.htr 0 1 6 (by decide) (by decide) with h778 | h778
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h779 | h779
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h780 | h780
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h781 | h781
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h782 | h782
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h783 | h783
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h784 | h784
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h785 | h785
                                · linarith only [h775, h785, hlam]
                                · linarith only [h784, h785, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                              · linarith only [h784, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h783, hlam, p0_0]
                          · linarith only [h782, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h781, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h731, h776, h780, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h779, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h679, h776, h778, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h777, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h796 | h796
                · rcases m.htr 0 1 6 (by decide) (by decide) with h797 | h797
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h798 | h798
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h799 | h799
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h800 | h800
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h801 | h801
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h802 | h802
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h803 | h803
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h804 | h804
                                · linarith only [h775, h804, hlam]
                                · linarith only [h803, h804, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                              · linarith only [h803, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h802, hlam, p0_0]
                          · linarith only [h801, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h800, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h731, h799, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h798, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h679, h775, h797, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h796, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h815 | h815
              · rcases m.htr 0 1 2 (by decide) (by decide) with h816 | h816
                · rcases m.htr 0 1 6 (by decide) (by decide) with h817 | h817
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h818 | h818
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h819 | h819
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h820 | h820
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h821 | h821
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h822 | h822
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h823 | h823
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h824 | h824
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h825 | h825
                                  · linarith only [h815, h825, hlam]
                                  · linarith only [h825, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4]
                                · linarith only [h775, h824, hc04, hc06, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h823, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h822, hlam, p0_0]
                          · linarith only [h821, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h820, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h731, h815, h819, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h818, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h679, h815, h817, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h816, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h837 | h837
                · rcases m.htr 0 1 6 (by decide) (by decide) with h838 | h838
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h839 | h839
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h840 | h840
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h841 | h841
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h842 | h842
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h843 | h843
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h844 | h844
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h845 | h845
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h846 | h846
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h847 | h847
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h848 | h848
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h849 | h849
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h850 | h850
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h851 | h851
                                            · linarith only [h679, h851, hlam]
                                            · linarith only [h837, h839, h841, h844, h846, h851, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h731, h837, h839, h841, h844, h846, h850, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h855 | h855
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h856 | h856
                                            · linarith only [h679, h856, hlam]
                                            · linarith only [h837, h839, h841, h844, h846, h847, h856, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h731, h837, h839, h841, h844, h846, h847, h855, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h860 | h860
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h861 | h861
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h862 | h862
                                            · linarith only [h679, h862, hlam]
                                            · linarith only [h837, h839, h841, h844, h846, h847, h862, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h731, h837, h839, h841, h844, h846, h847, h861, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h866 | h866
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h867 | h867
                                            · linarith only [h679, h867, hlam]
                                            · linarith only [h837, h839, h841, h844, h846, h847, h867, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h731, h837, h839, h841, h844, h846, h847, h866, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h871 | h871
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h872 | h872
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h873 | h873
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h874 | h874
                                            · linarith only [h679, h874, hlam]
                                            · linarith only [h837, h839, h841, h844, h846, h847, h871, h874, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h731, h837, h839, h841, h844, h846, h871, h873, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h878 | h878
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h879 | h879
                                            · linarith only [h679, h879, hlam]
                                            · linarith only [h837, h839, h841, h844, h846, h847, h871, h879, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h731, h837, h839, h841, h844, h846, h871, h878, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h883 | h883
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h884 | h884
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h885 | h885
                                            · linarith only [h679, h885, hlam]
                                            · linarith only [h837, h839, h841, h844, h846, h847, h885, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h731, h837, h839, h841, h844, h846, h883, h884, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h889 | h889
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h890 | h890
                                            · linarith only [h679, h890, hlam]
                                            · linarith only [h837, h839, h841, h844, h846, h847, h890, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h731, h837, h839, h841, h844, h846, h889, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h815, h846, hc05, hc06, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                · linarith only [h775, h837, h839, h843, h845, hc01, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h844, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h843, hlam, p0_0]
                          · linarith only [h842, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h841, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h731, h840, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h839, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h838, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h837, hc12, hlam, hphi, ht01, u0ehi0]
    · linarith only [h678, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h905 | h905
    · rcases p0_3 (m.d 1 6) (by simp) with h906 | h906
      · rcases p0_3 (m.d 2 6) (by simp) with h907 | h907
        · rcases p0_3 (m.d 3 6) (by simp) with h908 | h908
          · rcases p0_3 (m.d 4 6) (by simp) with h909 | h909
            · linarith only [h909, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h911 | h911
              · rcases m.htr 0 1 2 (by decide) (by decide) with h912 | h912
                · rcases m.htr 0 1 6 (by decide) (by decide) with h913 | h913
                  · linarith only [h906, h913, hlam]
                  · linarith only [h912, h913, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h912, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h917 | h917
                · rcases m.htr 0 1 6 (by decide) (by decide) with h918 | h918
                  · linarith only [h906, h918, hlam]
                  · linarith only [h917, h918, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h917, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h922 | h922
            · linarith only [h922, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h924 | h924
              · rcases m.htr 0 1 2 (by decide) (by decide) with h925 | h925
                · rcases m.htr 0 1 6 (by decide) (by decide) with h926 | h926
                  · linarith only [h906, h926, hlam]
                  · linarith only [h925, h926, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h925, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h930 | h930
                · rcases m.htr 0 1 6 (by decide) (by decide) with h931 | h931
                  · linarith only [h906, h931, hlam]
                  · linarith only [h930, h931, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h930, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h935 | h935
          · rcases p0_3 (m.d 4 6) (by simp) with h936 | h936
            · linarith only [h936, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h938 | h938
              · rcases m.htr 0 1 2 (by decide) (by decide) with h939 | h939
                · rcases m.htr 0 1 6 (by decide) (by decide) with h940 | h940
                  · linarith only [h906, h940, hlam]
                  · linarith only [h939, h940, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h939, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h944 | h944
                · rcases m.htr 0 1 6 (by decide) (by decide) with h945 | h945
                  · linarith only [h906, h945, hlam]
                  · linarith only [h944, h945, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h944, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h949 | h949
            · linarith only [h949, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h951 | h951
              · rcases m.htr 0 1 2 (by decide) (by decide) with h952 | h952
                · rcases m.htr 0 1 6 (by decide) (by decide) with h953 | h953
                  · linarith only [h906, h953, hlam]
                  · linarith only [h952, h953, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h952, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h957 | h957
                · rcases m.htr 0 1 6 (by decide) (by decide) with h958 | h958
                  · linarith only [h906, h958, hlam]
                  · linarith only [h957, h958, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h957, hc12, hlam, hphi, ht01, u0ehi0]
      · rcases p0_3 (m.d 2 6) (by simp) with h962 | h962
        · rcases p0_3 (m.d 3 6) (by simp) with h963 | h963
          · rcases p0_3 (m.d 4 6) (by simp) with h964 | h964
            · linarith only [h964, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h966 | h966
              · rcases m.htr 0 1 2 (by decide) (by decide) with h967 | h967
                · rcases m.htr 0 1 6 (by decide) (by decide) with h968 | h968
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h969 | h969
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h970 | h970
                      · linarith only [h962, h970, hlam]
                      · linarith only [h969, h970, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h969, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h906, h968, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h967, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h976 | h976
                · rcases m.htr 0 1 6 (by decide) (by decide) with h977 | h977
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h978 | h978
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h979 | h979
                      · linarith only [h962, h979, hlam]
                      · linarith only [h978, h979, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h978, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h906, h977, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h976, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h985 | h985
            · linarith only [h985, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h987 | h987
              · rcases m.htr 0 1 2 (by decide) (by decide) with h988 | h988
                · rcases m.htr 0 1 6 (by decide) (by decide) with h989 | h989
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h990 | h990
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h991 | h991
                      · linarith only [h962, h991, hlam]
                      · linarith only [h990, h991, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h990, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h906, h987, h989, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h988, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h997 | h997
                · rcases m.htr 0 1 6 (by decide) (by decide) with h998 | h998
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h999 | h999
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1000 | h1000
                      · linarith only [h1000, h962, hlam]
                      · linarith only [h1000, h999, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h999, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h906, h998, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h997, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1006 | h1006
          · rcases p0_3 (m.d 4 6) (by simp) with h1007 | h1007
            · linarith only [h1007, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1009 | h1009
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1010 | h1010
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1011 | h1011
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1012 | h1012
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1013 | h1013
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1014 | h1014
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1015 | h1015
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h1016 | h1016
                            · linarith only [h1006, h1016, hlam]
                            · linarith only [h1014, h1016, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h1014, h1015, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1014, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h1009, h1013, h962, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1012, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1009, h1011, h906, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h1010, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1025 | h1025
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1026 | h1026
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1027 | h1027
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1028 | h1028
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1029 | h1029
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1030 | h1030
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h1031 | h1031
                            · linarith only [h1006, h1031, hlam]
                            · linarith only [h1029, h1031, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h1029, h1030, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1029, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h1028, h962, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1027, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1006, h1026, h906, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h1025, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1040 | h1040
            · linarith only [h1040, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1042 | h1042
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1043 | h1043
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1044 | h1044
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1045 | h1045
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1046 | h1046
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1047 | h1047
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1048 | h1048
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h1049 | h1049
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h1050 | h1050
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h1051 | h1051
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h1052 | h1052
                                  · linarith only [h1042, h1052, hlam]
                                  · linarith only [h1052, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4]
                                · linarith only [h1051, hlam, p0_0]
                              · linarith only [h1050, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h1006, h1043, h1046, h1047, h1049, hc01, hlam, hphi, p0_1, u0ehi3]
                          · linarith only [h1047, h1048, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1047, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h1042, h1046, h962, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1045, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1042, h1044, h906, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h1043, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1064 | h1064
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1065 | h1065
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1066 | h1066
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1067 | h1067
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1068 | h1068
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1069 | h1069
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h1070 | h1070
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h1071 | h1071
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h1072 | h1072
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h1073 | h1073
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1074 | h1074
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1075 | h1075
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1076 | h1076
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1077 | h1077
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1078 | h1078
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1079 | h1079
                                              · linarith only [h1079, h906, hlam]
                                              · linarith only [h1064, h1066, h1068, h1071, h1073, h1079, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1006, h1064, h1066, h1068, h1071, h1073, h1078, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1064, h1066, h1068, h1071, h1073, h1077, h962, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1084 | h1084
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1085 | h1085
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1086 | h1086
                                              · linarith only [h1086, h906, hlam]
                                              · linarith only [h1064, h1066, h1068, h1071, h1073, h1075, h1086, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1006, h1064, h1066, h1068, h1071, h1073, h1085, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1064, h1066, h1068, h1071, h1073, h1074, h1084, h962, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1091 | h1091
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1092 | h1092
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1093 | h1093
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1094 | h1094
                                              · linarith only [h1094, h906, hlam]
                                              · linarith only [h1064, h1066, h1068, h1071, h1073, h1074, h1075, h1094, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1006, h1064, h1066, h1068, h1071, h1073, h1093, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1064, h1066, h1068, h1071, h1073, h1074, h1092, h962, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1099 | h1099
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1100 | h1100
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1101 | h1101
                                              · linarith only [h1101, h906, hlam]
                                              · linarith only [h1064, h1066, h1068, h1071, h1073, h1074, h1075, h1101, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1006, h1064, h1066, h1068, h1071, h1073, h1100, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1064, h1066, h1068, h1071, h1073, h1074, h1099, h962, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1106 | h1106
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1107 | h1107
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1108 | h1108
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1109 | h1109
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1110 | h1110
                                              · linarith only [h1110, h906, hlam]
                                              · linarith only [h1064, h1066, h1068, h1071, h1073, h1110, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1006, h1064, h1066, h1068, h1071, h1073, h1109, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1064, h1066, h1068, h1071, h1073, h1106, h1108, h962, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1115 | h1115
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1116 | h1116
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1117 | h1117
                                              · linarith only [h1117, h906, hlam]
                                              · linarith only [h1064, h1066, h1068, h1071, h1073, h1106, h1117, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1006, h1064, h1066, h1068, h1071, h1073, h1116, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1064, h1066, h1068, h1071, h1073, h1106, h1115, h962, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1122 | h1122
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1123 | h1123
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1124 | h1124
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1125 | h1125
                                              · linarith only [h1125, h906, hlam]
                                              · linarith only [h1064, h1066, h1068, h1071, h1073, h1106, h1125, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1006, h1064, h1066, h1068, h1071, h1073, h1124, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1064, h1066, h1068, h1071, h1073, h1122, h1123, h962, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1130 | h1130
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1131 | h1131
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1132 | h1132
                                              · linarith only [h1132, h906, hlam]
                                              · linarith only [h1064, h1066, h1068, h1071, h1073, h1106, h1132, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1006, h1064, h1066, h1068, h1071, h1073, h1131, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1064, h1066, h1068, h1071, h1073, h1130, h962, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h1042, h1073, hc05, hc06, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                · linarith only [h1072, hlam, p0_0]
                              · linarith only [h1071, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h1006, h1070, hc03, hc06, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1068, h1069, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1068, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h1067, h962, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1066, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1065, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1064, hc12, hlam, hphi, ht01, u0ehi0]
    · linarith only [h905, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1148 | h1148
    · rcases p0_3 (m.d 1 6) (by simp) with h1149 | h1149
      · rcases p0_3 (m.d 2 6) (by simp) with h1150 | h1150
        · rcases p0_3 (m.d 3 6) (by simp) with h1151 | h1151
          · rcases p0_3 (m.d 4 6) (by simp) with h1152 | h1152
            · rcases p0_3 (m.d 5 6) (by simp) with h1153 | h1153
              · linarith only [h1153, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1155 | h1155
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1156 | h1156
                  · linarith only [h1149, h1156, hlam]
                  · linarith only [h1155, h1156, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h1155, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1160 | h1160
              · linarith only [h1160, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1162 | h1162
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1163 | h1163
                  · linarith only [h1149, h1163, hlam]
                  · linarith only [h1162, h1163, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h1162, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1167 | h1167
            · rcases p0_3 (m.d 5 6) (by simp) with h1168 | h1168
              · linarith only [h1168, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1170 | h1170
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1171 | h1171
                  · linarith only [h1149, h1171, hlam]
                  · linarith only [h1170, h1171, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h1170, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1175 | h1175
              · linarith only [h1175, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1177 | h1177
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1178 | h1178
                  · linarith only [h1149, h1178, hlam]
                  · linarith only [h1177, h1178, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h1177, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1182 | h1182
          · rcases p0_3 (m.d 4 6) (by simp) with h1183 | h1183
            · rcases p0_3 (m.d 5 6) (by simp) with h1184 | h1184
              · linarith only [h1184, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1186 | h1186
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1187 | h1187
                  · linarith only [h1149, h1187, hlam]
                  · linarith only [h1186, h1187, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h1186, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1191 | h1191
              · linarith only [h1191, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1193 | h1193
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1194 | h1194
                  · linarith only [h1149, h1194, hlam]
                  · linarith only [h1193, h1194, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h1193, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1198 | h1198
            · rcases p0_3 (m.d 5 6) (by simp) with h1199 | h1199
              · linarith only [h1199, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1201 | h1201
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1202 | h1202
                  · linarith only [h1149, h1202, hlam]
                  · linarith only [h1201, h1202, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h1201, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1206 | h1206
              · linarith only [h1206, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1208 | h1208
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1209 | h1209
                  · linarith only [h1149, h1209, hlam]
                  · linarith only [h1208, h1209, hc16, hlam, hphi, ht01, u0ehi1]
                · linarith only [h1208, hc12, hlam, hphi, ht01, u0ehi0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1213 | h1213
        · rcases p0_3 (m.d 3 6) (by simp) with h1214 | h1214
          · rcases p0_3 (m.d 4 6) (by simp) with h1215 | h1215
            · rcases p0_3 (m.d 5 6) (by simp) with h1216 | h1216
              · linarith only [h1216, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1218 | h1218
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1219 | h1219
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1220 | h1220
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1221 | h1221
                      · linarith only [h1213, h1221, hlam]
                      · linarith only [h1220, h1221, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h1220, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1149, h1219, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1218, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1227 | h1227
              · linarith only [h1227, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1229 | h1229
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1230 | h1230
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1231 | h1231
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1232 | h1232
                      · linarith only [h1213, h1232, hlam]
                      · linarith only [h1231, h1232, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h1231, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1149, h1230, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1229, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1238 | h1238
            · rcases p0_3 (m.d 5 6) (by simp) with h1239 | h1239
              · linarith only [h1239, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1241 | h1241
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1242 | h1242
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1243 | h1243
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1244 | h1244
                      · linarith only [h1213, h1244, hlam]
                      · linarith only [h1243, h1244, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h1243, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1149, h1238, h1242, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h1241, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1250 | h1250
              · linarith only [h1250, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1252 | h1252
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1253 | h1253
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1254 | h1254
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1255 | h1255
                      · linarith only [h1213, h1255, hlam]
                      · linarith only [h1254, h1255, hc26, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h1254, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1149, h1253, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1252, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1261 | h1261
          · rcases p0_3 (m.d 4 6) (by simp) with h1262 | h1262
            · rcases p0_3 (m.d 5 6) (by simp) with h1263 | h1263
              · linarith only [h1263, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1265 | h1265
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1266 | h1266
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1267 | h1267
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1268 | h1268
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1269 | h1269
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1270 | h1270
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h1271 | h1271
                            · linarith only [h1261, h1271, hlam]
                            · linarith only [h1269, h1271, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h1269, h1270, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1269, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h1213, h1262, h1268, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h1267, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1149, h1262, h1266, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h1265, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1280 | h1280
              · linarith only [h1280, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1282 | h1282
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1283 | h1283
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1284 | h1284
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1285 | h1285
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1286 | h1286
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1287 | h1287
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h1288 | h1288
                            · linarith only [h1261, h1288, hlam]
                            · linarith only [h1286, h1288, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h1286, h1287, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1286, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h1213, h1285, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1284, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1149, h1261, h1283, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h1282, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1297 | h1297
            · rcases p0_3 (m.d 5 6) (by simp) with h1298 | h1298
              · linarith only [h1298, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1300 | h1300
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1301 | h1301
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1302 | h1302
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1303 | h1303
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1304 | h1304
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1305 | h1305
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h1306 | h1306
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h1307 | h1307
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h1308 | h1308
                                · linarith only [h1297, h1308, hlam]
                                · linarith only [h1307, h1308, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                              · linarith only [h1307, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h1261, h1306, hc03, hc06, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1304, h1305, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1304, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h1213, h1297, h1303, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h1302, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1149, h1297, h1301, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h1300, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1319 | h1319
              · linarith only [h1319, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1321 | h1321
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1322 | h1322
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1323 | h1323
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1324 | h1324
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1325 | h1325
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1326 | h1326
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h1327 | h1327
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h1328 | h1328
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h1329 | h1329
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h1330 | h1330
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1331 | h1331
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1332 | h1332
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1333 | h1333
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1334 | h1334
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1335 | h1335
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1336 | h1336
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h1337 | h1337
                                                · linarith only [h1149, h1337, hlam]
                                                · linarith only [h1321, h1323, h1325, h1328, h1330, h1337, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                              · linarith only [h1297, h1321, h1323, h1325, h1328, h1330, h1336, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1261, h1321, h1323, h1325, h1328, h1330, h1335, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1213, h1321, h1323, h1325, h1328, h1330, h1334, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1343 | h1343
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1344 | h1344
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1345 | h1345
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h1346 | h1346
                                                · linarith only [h1149, h1346, hlam]
                                                · linarith only [h1321, h1323, h1325, h1328, h1330, h1331, h1333, h1346, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                              · linarith only [h1297, h1321, h1323, h1325, h1328, h1330, h1345, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1261, h1321, h1323, h1325, h1328, h1330, h1344, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1213, h1321, h1323, h1325, h1328, h1330, h1331, h1343, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1352 | h1352
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1353 | h1353
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1354 | h1354
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1355 | h1355
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h1356 | h1356
                                                · linarith only [h1149, h1356, hlam]
                                                · linarith only [h1321, h1323, h1325, h1328, h1330, h1356, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                              · linarith only [h1297, h1321, h1323, h1325, h1328, h1330, h1355, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1261, h1321, h1323, h1325, h1328, h1330, h1354, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1213, h1321, h1323, h1325, h1328, h1330, h1331, h1353, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1362 | h1362
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1363 | h1363
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1364 | h1364
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h1365 | h1365
                                                · linarith only [h1149, h1365, hlam]
                                                · linarith only [h1321, h1323, h1325, h1328, h1330, h1331, h1352, h1365, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                              · linarith only [h1297, h1321, h1323, h1325, h1328, h1330, h1364, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1261, h1321, h1323, h1325, h1328, h1330, h1363, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1213, h1321, h1323, h1325, h1328, h1330, h1331, h1362, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1371 | h1371
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1372 | h1372
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1373 | h1373
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1374 | h1374
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1375 | h1375
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h1376 | h1376
                                                · linarith only [h1149, h1376, hlam]
                                                · linarith only [h1321, h1323, h1325, h1328, h1330, h1376, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                              · linarith only [h1297, h1321, h1323, h1325, h1328, h1330, h1375, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1261, h1321, h1323, h1325, h1328, h1330, h1374, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1213, h1321, h1323, h1325, h1328, h1330, h1371, h1373, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1382 | h1382
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1383 | h1383
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1384 | h1384
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h1385 | h1385
                                                · linarith only [h1149, h1385, hlam]
                                                · linarith only [h1321, h1323, h1325, h1328, h1330, h1371, h1372, h1385, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                              · linarith only [h1297, h1321, h1323, h1325, h1328, h1330, h1384, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1261, h1321, h1323, h1325, h1328, h1330, h1383, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1213, h1321, h1323, h1325, h1328, h1330, h1371, h1382, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1391 | h1391
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1392 | h1392
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1393 | h1393
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1394 | h1394
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h1395 | h1395
                                                · linarith only [h1149, h1395, hlam]
                                                · linarith only [h1321, h1323, h1325, h1328, h1330, h1395, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                              · linarith only [h1297, h1321, h1323, h1325, h1328, h1330, h1394, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1261, h1321, h1323, h1325, h1328, h1330, h1393, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1213, h1321, h1323, h1325, h1328, h1330, h1392, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 2 6 (by decide) (by decide) with h1401 | h1401
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1402 | h1402
                                            · rcases m.htr 1 4 6 (by decide) (by decide) with h1403 | h1403
                                              · rcases m.htr 1 5 6 (by decide) (by decide) with h1404 | h1404
                                                · linarith only [h1149, h1404, hlam]
                                                · linarith only [h1321, h1323, h1325, h1328, h1330, h1391, h1401, h1404, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                              · linarith only [h1297, h1321, h1323, h1325, h1328, h1330, h1403, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h1261, h1321, h1323, h1325, h1328, h1330, h1402, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · linarith only [h1213, h1321, h1323, h1325, h1328, h1330, h1401, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h1330, hlam, p0_0]
                                · linarith only [h1297, h1329, hc04, hc06, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1328, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h1261, h1327, hc03, hc06, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1325, h1326, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1325, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h1213, h1324, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1323, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1322, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1321, hc12, hlam, hphi, ht01, u0ehi0]
    · linarith only [h1148, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1423 | h1423
    · rcases p0_3 (m.d 1 6) (by simp) with h1424 | h1424
      · rcases p0_3 (m.d 2 6) (by simp) with h1425 | h1425
        · linarith only [h1425, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1427 | h1427
          · rcases p0_3 (m.d 4 6) (by simp) with h1428 | h1428
            · rcases p0_3 (m.d 5 6) (by simp) with h1429 | h1429
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1430 | h1430
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1431 | h1431
                  · linarith only [h1431, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1423, h1431, hlam]
                · linarith only [h1430, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1435 | h1435
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1436 | h1436
                  · linarith only [h1436, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1423, h1436, hlam]
                · linarith only [h1435, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1440 | h1440
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1441 | h1441
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1442 | h1442
                  · linarith only [h1442, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1423, h1442, hlam]
                · linarith only [h1441, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1446 | h1446
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1447 | h1447
                  · linarith only [h1447, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1423, h1447, hlam]
                · linarith only [h1446, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1451 | h1451
            · rcases p0_3 (m.d 5 6) (by simp) with h1452 | h1452
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1453 | h1453
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1454 | h1454
                  · linarith only [h1454, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1423, h1454, hlam]
                · linarith only [h1453, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1458 | h1458
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1459 | h1459
                  · linarith only [h1459, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1423, h1459, hlam]
                · linarith only [h1458, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1463 | h1463
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1464 | h1464
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1465 | h1465
                  · linarith only [h1465, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1423, h1465, hlam]
                · linarith only [h1464, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1469 | h1469
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1470 | h1470
                  · linarith only [h1470, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1423, h1470, hlam]
                · linarith only [h1469, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h1424, hlam, p0_0]
    · linarith only [h1423, hc16, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1476 | h1476
    · rcases p0_3 (m.d 1 6) (by simp) with h1477 | h1477
      · rcases p0_3 (m.d 2 6) (by simp) with h1478 | h1478
        · rcases p0_3 (m.d 3 6) (by simp) with h1479 | h1479
          · linarith only [h1479, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1481 | h1481
            · rcases p0_3 (m.d 5 6) (by simp) with h1482 | h1482
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1483 | h1483
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1484 | h1484
                  · linarith only [h1484, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1476, h1484, hlam]
                · linarith only [h1483, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1488 | h1488
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1489 | h1489
                  · linarith only [h1489, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1476, h1489, hlam]
                · linarith only [h1488, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1493 | h1493
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1494 | h1494
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1495 | h1495
                  · linarith only [h1495, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1476, h1495, hlam]
                · linarith only [h1494, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1499 | h1499
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1500 | h1500
                  · linarith only [h1500, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1476, h1500, hlam]
                · linarith only [h1499, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1504 | h1504
          · linarith only [h1504, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1506 | h1506
            · rcases p0_3 (m.d 5 6) (by simp) with h1507 | h1507
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1508 | h1508
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1509 | h1509
                  · linarith only [h1509, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1476, h1509, hlam]
                · linarith only [h1508, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1513 | h1513
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1514 | h1514
                  · linarith only [h1514, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1476, h1514, hlam]
                · linarith only [h1513, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1518 | h1518
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1519 | h1519
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1520 | h1520
                  · linarith only [h1520, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1476, h1520, hlam]
                · linarith only [h1519, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1524 | h1524
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1525 | h1525
                  · linarith only [h1525, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1476, h1525, hlam]
                · linarith only [h1524, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h1477, hlam, p0_0]
    · linarith only [h1476, hc16, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1531 | h1531
    · rcases p0_3 (m.d 1 6) (by simp) with h1532 | h1532
      · rcases p0_3 (m.d 2 6) (by simp) with h1533 | h1533
        · rcases p0_3 (m.d 3 6) (by simp) with h1534 | h1534
          · rcases p0_3 (m.d 4 6) (by simp) with h1535 | h1535
            · linarith only [h1535, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1537 | h1537
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1538 | h1538
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1539 | h1539
                  · linarith only [h1539, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1531, h1539, hlam]
                · linarith only [h1538, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1543 | h1543
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1544 | h1544
                  · linarith only [h1544, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1531, h1544, hlam]
                · linarith only [h1543, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1548 | h1548
            · linarith only [h1548, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1550 | h1550
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1551 | h1551
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1552 | h1552
                  · linarith only [h1552, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1531, h1552, hlam]
                · linarith only [h1551, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1556 | h1556
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1557 | h1557
                  · linarith only [h1557, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1531, h1557, hlam]
                · linarith only [h1556, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1561 | h1561
          · rcases p0_3 (m.d 4 6) (by simp) with h1562 | h1562
            · linarith only [h1562, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1564 | h1564
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1565 | h1565
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1566 | h1566
                  · linarith only [h1566, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1531, h1566, hlam]
                · linarith only [h1565, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1570 | h1570
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1571 | h1571
                  · linarith only [h1571, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1531, h1571, hlam]
                · linarith only [h1570, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1575 | h1575
            · linarith only [h1575, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1577 | h1577
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1578 | h1578
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1579 | h1579
                  · linarith only [h1579, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1531, h1579, hlam]
                · linarith only [h1578, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1583 | h1583
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1584 | h1584
                  · linarith only [h1584, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1531, h1584, hlam]
                · linarith only [h1583, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h1532, hlam, p0_0]
    · linarith only [h1531, hc16, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1590 | h1590
    · rcases p0_3 (m.d 1 6) (by simp) with h1591 | h1591
      · rcases p0_3 (m.d 2 6) (by simp) with h1592 | h1592
        · rcases p0_3 (m.d 3 6) (by simp) with h1593 | h1593
          · rcases p0_3 (m.d 4 6) (by simp) with h1594 | h1594
            · rcases p0_3 (m.d 5 6) (by simp) with h1595 | h1595
              · linarith only [h1595, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1597 | h1597
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1598 | h1598
                  · linarith only [h1598, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1590, h1598, hlam]
                · linarith only [h1597, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1602 | h1602
              · linarith only [h1602, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1604 | h1604
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1605 | h1605
                  · linarith only [h1605, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1590, h1605, hlam]
                · linarith only [h1604, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1609 | h1609
            · rcases p0_3 (m.d 5 6) (by simp) with h1610 | h1610
              · linarith only [h1610, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1612 | h1612
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1613 | h1613
                  · linarith only [h1613, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1590, h1613, hlam]
                · linarith only [h1612, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1617 | h1617
              · linarith only [h1617, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1619 | h1619
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1620 | h1620
                  · linarith only [h1620, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1590, h1620, hlam]
                · linarith only [h1619, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1624 | h1624
          · rcases p0_3 (m.d 4 6) (by simp) with h1625 | h1625
            · rcases p0_3 (m.d 5 6) (by simp) with h1626 | h1626
              · linarith only [h1626, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1628 | h1628
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1629 | h1629
                  · linarith only [h1629, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1590, h1629, hlam]
                · linarith only [h1628, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1633 | h1633
              · linarith only [h1633, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1635 | h1635
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1636 | h1636
                  · linarith only [h1636, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1590, h1636, hlam]
                · linarith only [h1635, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1640 | h1640
            · rcases p0_3 (m.d 5 6) (by simp) with h1641 | h1641
              · linarith only [h1641, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1643 | h1643
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1644 | h1644
                  · linarith only [h1644, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1590, h1644, hlam]
                · linarith only [h1643, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1648 | h1648
              · linarith only [h1648, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1650 | h1650
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1651 | h1651
                  · linarith only [h1651, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1590, h1651, hlam]
                · linarith only [h1650, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h1591, hlam, p0_0]
    · linarith only [h1590, hc16, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1658 | h1658
    · rcases p0_3 (m.d 1 6) (by simp) with h1659 | h1659
      · linarith only [h1659, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1661 | h1661
        · rcases p0_3 (m.d 3 6) (by simp) with h1662 | h1662
          · rcases p0_3 (m.d 4 6) (by simp) with h1663 | h1663
            · rcases p0_3 (m.d 5 6) (by simp) with h1664 | h1664
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1665 | h1665
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1666 | h1666
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1667 | h1667
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1668 | h1668
                      · linarith only [h1668, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1658, h1668, hlam]
                    · linarith only [h1667, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1665, h1666, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1665, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1674 | h1674
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1675 | h1675
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1676 | h1676
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1677 | h1677
                      · linarith only [h1677, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1658, h1677, hlam]
                    · linarith only [h1676, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1674, h1675, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1674, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1683 | h1683
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1684 | h1684
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1685 | h1685
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1686 | h1686
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1687 | h1687
                      · linarith only [h1687, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1658, h1687, hlam]
                    · linarith only [h1686, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1684, h1685, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1684, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1693 | h1693
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1694 | h1694
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1695 | h1695
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1696 | h1696
                      · linarith only [h1696, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1658, h1696, hlam]
                    · linarith only [h1695, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1693, h1694, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1693, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1702 | h1702
            · rcases p0_3 (m.d 5 6) (by simp) with h1703 | h1703
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1704 | h1704
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1705 | h1705
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1706 | h1706
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1707 | h1707
                      · linarith only [h1707, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1658, h1707, hlam]
                    · linarith only [h1706, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1704, h1705, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1704, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1713 | h1713
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1714 | h1714
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1715 | h1715
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1716 | h1716
                      · linarith only [h1716, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1658, h1716, hlam]
                    · linarith only [h1715, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1713, h1714, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1713, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1722 | h1722
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1723 | h1723
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1724 | h1724
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1725 | h1725
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1726 | h1726
                      · linarith only [h1726, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1658, h1726, hlam]
                    · linarith only [h1725, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1723, h1724, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1723, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1732 | h1732
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1733 | h1733
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1734 | h1734
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1735 | h1735
                      · linarith only [h1735, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1658, h1735, hlam]
                    · linarith only [h1734, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1732, h1733, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1732, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h1661, hlam, p0_0]
    · linarith only [h1658, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1744 | h1744
    · rcases p0_3 (m.d 1 6) (by simp) with h1745 | h1745
      · rcases p0_3 (m.d 2 6) (by simp) with h1746 | h1746
        · rcases p0_3 (m.d 3 6) (by simp) with h1747 | h1747
          · linarith only [h1747, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1749 | h1749
            · rcases p0_3 (m.d 5 6) (by simp) with h1750 | h1750
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1751 | h1751
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1752 | h1752
                  · linarith only [h1745, h1752, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1752, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1751, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1756 | h1756
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1757 | h1757
                  · linarith only [h1745, h1757, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1757, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1756, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1761 | h1761
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1762 | h1762
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1763 | h1763
                  · linarith only [h1745, h1763, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1763, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1762, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1767 | h1767
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1768 | h1768
                  · linarith only [h1745, h1768, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1768, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1767, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h1746, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1773 | h1773
        · rcases p0_3 (m.d 3 6) (by simp) with h1774 | h1774
          · linarith only [h1774, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1776 | h1776
            · rcases p0_3 (m.d 5 6) (by simp) with h1777 | h1777
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1778 | h1778
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1779 | h1779
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1780 | h1780
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1781 | h1781
                      · linarith only [h1781, hc02, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1744, h1781, hlam]
                    · linarith only [h1780, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1745, h1778, h1779, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1778, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1787 | h1787
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1788 | h1788
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1789 | h1789
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1790 | h1790
                      · linarith only [h1745, h1790, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1744, h1790, hlam]
                    · linarith only [h1789, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1745, h1787, h1788, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1787, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1796 | h1796
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1797 | h1797
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1798 | h1798
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1799 | h1799
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1800 | h1800
                      · linarith only [h1745, h1800, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1744, h1800, hlam]
                    · linarith only [h1799, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1745, h1797, h1798, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1797, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1806 | h1806
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1807 | h1807
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1808 | h1808
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1809 | h1809
                      · linarith only [h1745, h1809, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1744, h1809, hlam]
                    · linarith only [h1808, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1745, h1806, h1807, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1806, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h1773, hlam, p0_0]
    · linarith only [h1744, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1817 | h1817
    · rcases p0_3 (m.d 1 6) (by simp) with h1818 | h1818
      · rcases p0_3 (m.d 2 6) (by simp) with h1819 | h1819
        · rcases p0_3 (m.d 3 6) (by simp) with h1820 | h1820
          · rcases p0_3 (m.d 4 6) (by simp) with h1821 | h1821
            · linarith only [h1821, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1823 | h1823
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1824 | h1824
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1825 | h1825
                  · linarith only [h1818, h1825, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1825, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1824, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1829 | h1829
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1830 | h1830
                  · linarith only [h1818, h1830, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1830, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1829, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1834 | h1834
            · linarith only [h1834, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1836 | h1836
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1837 | h1837
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1838 | h1838
                  · linarith only [h1818, h1838, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1838, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1837, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1842 | h1842
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1843 | h1843
                  · linarith only [h1818, h1843, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1843, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1842, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h1819, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1848 | h1848
        · rcases p0_3 (m.d 3 6) (by simp) with h1849 | h1849
          · rcases p0_3 (m.d 4 6) (by simp) with h1850 | h1850
            · linarith only [h1850, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1852 | h1852
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1853 | h1853
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1854 | h1854
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1855 | h1855
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1856 | h1856
                      · linarith only [h1856, hc02, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1817, h1856, hlam]
                    · linarith only [h1855, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1818, h1853, h1854, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1853, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1862 | h1862
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1863 | h1863
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1864 | h1864
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1865 | h1865
                      · linarith only [h1818, h1865, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1817, h1865, hlam]
                    · linarith only [h1864, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1818, h1862, h1863, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1862, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1871 | h1871
            · linarith only [h1871, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1873 | h1873
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1874 | h1874
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1875 | h1875
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1876 | h1876
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1877 | h1877
                      · linarith only [h1818, h1877, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1817, h1877, hlam]
                    · linarith only [h1876, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1818, h1874, h1875, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1874, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1883 | h1883
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1884 | h1884
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1885 | h1885
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1886 | h1886
                      · linarith only [h1818, h1886, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1817, h1886, hlam]
                    · linarith only [h1885, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1818, h1883, h1884, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1883, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h1848, hlam, p0_0]
    · linarith only [h1817, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1894 | h1894
    · rcases p0_3 (m.d 1 6) (by simp) with h1895 | h1895
      · rcases p0_3 (m.d 2 6) (by simp) with h1896 | h1896
        · rcases p0_3 (m.d 3 6) (by simp) with h1897 | h1897
          · rcases p0_3 (m.d 4 6) (by simp) with h1898 | h1898
            · rcases p0_3 (m.d 5 6) (by simp) with h1899 | h1899
              · linarith only [h1899, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1901 | h1901
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1902 | h1902
                  · linarith only [h1895, h1902, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1902, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1901, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1906 | h1906
              · linarith only [h1906, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1908 | h1908
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1909 | h1909
                  · linarith only [h1895, h1909, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1909, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1908, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1913 | h1913
            · rcases p0_3 (m.d 5 6) (by simp) with h1914 | h1914
              · linarith only [h1914, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1916 | h1916
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1917 | h1917
                  · linarith only [h1895, h1917, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1917, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1916, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1921 | h1921
              · linarith only [h1921, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1923 | h1923
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1924 | h1924
                  · linarith only [h1895, h1924, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h1924, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h1923, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h1896, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1929 | h1929
        · rcases p0_3 (m.d 3 6) (by simp) with h1930 | h1930
          · rcases p0_3 (m.d 4 6) (by simp) with h1931 | h1931
            · rcases p0_3 (m.d 5 6) (by simp) with h1932 | h1932
              · linarith only [h1932, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1934 | h1934
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1935 | h1935
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1936 | h1936
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1937 | h1937
                      · linarith only [h1937, hc02, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1894, h1937, hlam]
                    · linarith only [h1936, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1895, h1934, h1935, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1934, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1943 | h1943
              · linarith only [h1943, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1945 | h1945
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1946 | h1946
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1947 | h1947
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1948 | h1948
                      · linarith only [h1895, h1948, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1894, h1948, hlam]
                    · linarith only [h1947, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1895, h1945, h1946, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1945, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1954 | h1954
            · rcases p0_3 (m.d 5 6) (by simp) with h1955 | h1955
              · linarith only [h1955, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1957 | h1957
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1958 | h1958
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1959 | h1959
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1960 | h1960
                      · linarith only [h1895, h1960, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1894, h1960, hlam]
                    · linarith only [h1959, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1895, h1957, h1958, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1957, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1966 | h1966
              · linarith only [h1966, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1968 | h1968
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1969 | h1969
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1970 | h1970
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1971 | h1971
                      · linarith only [h1895, h1971, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1894, h1971, hlam]
                    · linarith only [h1970, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1895, h1968, h1969, hc12, hc26, hlam, hphi, p0_1]
                · linarith only [h1968, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h1929, hlam, p0_0]
    · linarith only [h1894, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1980 | h1980
    · rcases p0_3 (m.d 1 6) (by simp) with h1981 | h1981
      · linarith only [h1981, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1983 | h1983
        · rcases p0_3 (m.d 3 6) (by simp) with h1984 | h1984
          · rcases p0_3 (m.d 4 6) (by simp) with h1985 | h1985
            · rcases p0_3 (m.d 5 6) (by simp) with h1986 | h1986
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1987 | h1987
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1988 | h1988
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1989 | h1989
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1990 | h1990
                      · linarith only [h1983, h1990, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1990, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h1989, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1980, h1988, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1987, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1996 | h1996
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1997 | h1997
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1998 | h1998
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1999 | h1999
                      · linarith only [h1983, h1999, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h1999, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h1998, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1980, h1997, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1996, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2005 | h2005
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2006 | h2006
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2007 | h2007
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2008 | h2008
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2009 | h2009
                      · linarith only [h1983, h2009, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2009, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2008, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1980, h2007, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2006, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2015 | h2015
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2016 | h2016
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2017 | h2017
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2018 | h2018
                      · linarith only [h1983, h2018, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2018, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2017, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1980, h2016, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2015, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h1984, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2025 | h2025
          · rcases p0_3 (m.d 4 6) (by simp) with h2026 | h2026
            · rcases p0_3 (m.d 5 6) (by simp) with h2027 | h2027
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2028 | h2028
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2029 | h2029
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2030 | h2030
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2031 | h2031
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2032 | h2032
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2033 | h2033
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2034 | h2034
                            · linarith only [h2034, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h1980, h2034, hlam]
                          · linarith only [h2033, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2032, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2031, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2030, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1980, h2029, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2028, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2043 | h2043
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2044 | h2044
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2045 | h2045
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2046 | h2046
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2047 | h2047
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2048 | h2048
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2049 | h2049
                            · linarith only [h2049, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h1980, h2049, hlam]
                          · linarith only [h2048, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2047, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2046, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2045, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1980, h2044, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2043, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2058 | h2058
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2059 | h2059
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2060 | h2060
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2061 | h2061
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2062 | h2062
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2063 | h2063
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2064 | h2064
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2065 | h2065
                            · linarith only [h2065, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h1980, h2065, hlam]
                          · linarith only [h2064, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2063, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2062, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2061, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h1980, h2060, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2059, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2074 | h2074
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2075 | h2075
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2076 | h2076
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2077 | h2077
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2078 | h2078
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2079 | h2079
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2080 | h2080
                            · linarith only [h2080, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h1980, h2080, hlam]
                          · linarith only [h2079, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2078, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h1980, h1983, h2077, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2076, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2075, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h2074, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2025, hlam, p0_0]
    · linarith only [h1980, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2091 | h2091
    · rcases p0_3 (m.d 1 6) (by simp) with h2092 | h2092
      · rcases p0_3 (m.d 2 6) (by simp) with h2093 | h2093
        · linarith only [h2093, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2095 | h2095
          · rcases p0_3 (m.d 4 6) (by simp) with h2096 | h2096
            · rcases p0_3 (m.d 5 6) (by simp) with h2097 | h2097
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2098 | h2098
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2099 | h2099
                  · linarith only [h2092, h2099, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2099, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2098, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2103 | h2103
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2104 | h2104
                  · linarith only [h2092, h2104, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2104, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2103, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2108 | h2108
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2109 | h2109
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2110 | h2110
                  · linarith only [h2092, h2110, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2110, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2109, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2114 | h2114
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2115 | h2115
                  · linarith only [h2092, h2115, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2115, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2114, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2095, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2120 | h2120
        · linarith only [h2120, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2122 | h2122
          · rcases p0_3 (m.d 4 6) (by simp) with h2123 | h2123
            · rcases p0_3 (m.d 5 6) (by simp) with h2124 | h2124
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2125 | h2125
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2126 | h2126
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2127 | h2127
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2128 | h2128
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2129 | h2129
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2130 | h2130
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2131 | h2131
                            · linarith only [h2131, hc03, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2091, h2131, hlam]
                          · linarith only [h2130, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2129, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2127, h2128, hc23, hc36, hlam, hphi, p0_1]
                    · linarith only [h2127, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2092, h2124, h2126, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2125, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2140 | h2140
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2141 | h2141
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2142 | h2142
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2143 | h2143
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2144 | h2144
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2145 | h2145
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2146 | h2146
                            · linarith only [h2092, h2146, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2091, h2146, hlam]
                          · linarith only [h2145, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2144, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2091, h2143, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2142, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2141, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2140, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2155 | h2155
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2156 | h2156
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2157 | h2157
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2158 | h2158
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2159 | h2159
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2160 | h2160
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2161 | h2161
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2162 | h2162
                            · linarith only [h2162, hc03, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2091, h2162, hlam]
                          · linarith only [h2161, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2160, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2158, h2159, hc23, hc36, hlam, hphi, p0_1]
                    · linarith only [h2158, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2092, h2155, h2157, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2156, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2171 | h2171
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2172 | h2172
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2173 | h2173
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2174 | h2174
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2175 | h2175
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2176 | h2176
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2177 | h2177
                            · linarith only [h2092, h2177, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2091, h2177, hlam]
                          · linarith only [h2176, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2175, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2091, h2174, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2173, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2172, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2171, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2122, hlam, p0_0]
    · linarith only [h2091, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2189 | h2189
    · rcases p0_3 (m.d 1 6) (by simp) with h2190 | h2190
      · rcases p0_3 (m.d 2 6) (by simp) with h2191 | h2191
        · rcases p0_3 (m.d 3 6) (by simp) with h2192 | h2192
          · rcases p0_3 (m.d 4 6) (by simp) with h2193 | h2193
            · linarith only [h2193, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2195 | h2195
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2196 | h2196
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2197 | h2197
                  · linarith only [h2190, h2197, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2197, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2196, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2201 | h2201
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2202 | h2202
                  · linarith only [h2190, h2202, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2202, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2201, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2192, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2207 | h2207
          · rcases p0_3 (m.d 4 6) (by simp) with h2208 | h2208
            · linarith only [h2208, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2210 | h2210
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2211 | h2211
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2212 | h2212
                  · linarith only [h2190, h2212, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2212, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2211, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2216 | h2216
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2217 | h2217
                  · linarith only [h2190, h2217, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2217, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2216, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2207, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2222 | h2222
        · rcases p0_3 (m.d 3 6) (by simp) with h2223 | h2223
          · rcases p0_3 (m.d 4 6) (by simp) with h2224 | h2224
            · linarith only [h2224, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2226 | h2226
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2227 | h2227
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2228 | h2228
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2229 | h2229
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2230 | h2230
                      · linarith only [h2222, h2230, hc02, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2230, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2229, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2189, h2190, h2228, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2227, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2236 | h2236
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2237 | h2237
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2238 | h2238
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2239 | h2239
                      · linarith only [h2190, h2222, h2239, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2239, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2238, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2189, h2190, h2237, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2236, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2223, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2246 | h2246
          · rcases p0_3 (m.d 4 6) (by simp) with h2247 | h2247
            · linarith only [h2247, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2249 | h2249
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2250 | h2250
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2251 | h2251
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2252 | h2252
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2253 | h2253
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2254 | h2254
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2255 | h2255
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2256 | h2256
                            · linarith only [h2190, h2256, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2189, h2256, hlam]
                          · linarith only [h2255, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2254, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2189, h2222, h2253, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2252, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2251, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2250, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2265 | h2265
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2266 | h2266
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2267 | h2267
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2268 | h2268
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2269 | h2269
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2270 | h2270
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2271 | h2271
                            · linarith only [h2190, h2271, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2189, h2271, hlam]
                          · linarith only [h2270, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2269, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2189, h2222, h2268, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2267, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2189, h2190, h2266, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2265, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2246, hlam, p0_0]
    · linarith only [h2189, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2282 | h2282
    · rcases p0_3 (m.d 1 6) (by simp) with h2283 | h2283
      · rcases p0_3 (m.d 2 6) (by simp) with h2284 | h2284
        · rcases p0_3 (m.d 3 6) (by simp) with h2285 | h2285
          · rcases p0_3 (m.d 4 6) (by simp) with h2286 | h2286
            · rcases p0_3 (m.d 5 6) (by simp) with h2287 | h2287
              · linarith only [h2287, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2289 | h2289
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2290 | h2290
                  · linarith only [h2283, h2290, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2290, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2289, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2294 | h2294
              · linarith only [h2294, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2296 | h2296
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2297 | h2297
                  · linarith only [h2283, h2297, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2297, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2296, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2285, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2302 | h2302
          · rcases p0_3 (m.d 4 6) (by simp) with h2303 | h2303
            · rcases p0_3 (m.d 5 6) (by simp) with h2304 | h2304
              · linarith only [h2304, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2306 | h2306
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2307 | h2307
                  · linarith only [h2283, h2307, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2307, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2306, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2311 | h2311
              · linarith only [h2311, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2313 | h2313
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2314 | h2314
                  · linarith only [h2283, h2314, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2314, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2313, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2302, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2319 | h2319
        · rcases p0_3 (m.d 3 6) (by simp) with h2320 | h2320
          · rcases p0_3 (m.d 4 6) (by simp) with h2321 | h2321
            · rcases p0_3 (m.d 5 6) (by simp) with h2322 | h2322
              · linarith only [h2322, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2324 | h2324
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2325 | h2325
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2326 | h2326
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2327 | h2327
                      · linarith only [h2319, h2327, hc02, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2327, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2326, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2282, h2283, h2325, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2324, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2333 | h2333
              · linarith only [h2333, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2335 | h2335
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2336 | h2336
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2337 | h2337
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2338 | h2338
                      · linarith only [h2283, h2319, h2338, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2338, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2337, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2282, h2283, h2336, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2335, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2320, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2345 | h2345
          · rcases p0_3 (m.d 4 6) (by simp) with h2346 | h2346
            · rcases p0_3 (m.d 5 6) (by simp) with h2347 | h2347
              · linarith only [h2347, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2349 | h2349
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2350 | h2350
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2351 | h2351
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2352 | h2352
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2353 | h2353
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2354 | h2354
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2355 | h2355
                            · linarith only [h2283, h2355, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2282, h2355, hlam]
                          · linarith only [h2354, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2353, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2319, h2352, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h2351, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2350, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2349, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2364 | h2364
              · linarith only [h2364, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2366 | h2366
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2367 | h2367
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2368 | h2368
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2369 | h2369
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2370 | h2370
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2371 | h2371
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2372 | h2372
                            · linarith only [h2319, h2372, hc03, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2282, h2372, hlam]
                          · linarith only [h2371, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2370, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2319, h2368, h2369, hc23, hc36, hlam, hphi, p0_1]
                    · linarith only [h2368, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2283, h2367, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h2366, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h2345, hlam, p0_0]
    · linarith only [h2282, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2384 | h2384
    · rcases p0_3 (m.d 1 6) (by simp) with h2385 | h2385
      · linarith only [h2385, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2387 | h2387
        · rcases p0_3 (m.d 3 6) (by simp) with h2388 | h2388
          · rcases p0_3 (m.d 4 6) (by simp) with h2389 | h2389
            · rcases p0_3 (m.d 5 6) (by simp) with h2390 | h2390
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2391 | h2391
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2392 | h2392
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2393 | h2393
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2394 | h2394
                      · linarith only [h2387, h2394, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2394, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2393, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2384, h2392, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2391, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2400 | h2400
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2401 | h2401
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2402 | h2402
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2403 | h2403
                      · linarith only [h2387, h2403, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2403, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2402, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2384, h2401, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2400, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2389, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2410 | h2410
            · rcases p0_3 (m.d 5 6) (by simp) with h2411 | h2411
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2412 | h2412
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2413 | h2413
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2414 | h2414
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2415 | h2415
                      · linarith only [h2387, h2415, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2415, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2414, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2384, h2413, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2412, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2421 | h2421
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2422 | h2422
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2423 | h2423
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2424 | h2424
                      · linarith only [h2387, h2424, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2424, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2423, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2422, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h2421, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2410, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2431 | h2431
          · rcases p0_3 (m.d 4 6) (by simp) with h2432 | h2432
            · rcases p0_3 (m.d 5 6) (by simp) with h2433 | h2433
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2434 | h2434
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2435 | h2435
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2436 | h2436
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2437 | h2437
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2438 | h2438
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2439 | h2439
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2440 | h2440
                            · linarith only [h2431, h2440, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2440, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2438, h2439, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2438, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2384, h2387, h2437, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2436, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2433, h2435, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2434, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2449 | h2449
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2450 | h2450
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2451 | h2451
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2452 | h2452
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2453 | h2453
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2454 | h2454
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2455 | h2455
                            · linarith only [h2431, h2455, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2455, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2453, h2454, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2453, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2384, h2387, h2452, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2451, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2450, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h2449, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2432, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2465 | h2465
            · rcases p0_3 (m.d 5 6) (by simp) with h2466 | h2466
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2467 | h2467
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2468 | h2468
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2469 | h2469
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2470 | h2470
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2471 | h2471
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2472 | h2472
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2473 | h2473
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h2474 | h2474
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h2475 | h2475
                                · linarith only [h2475, hc04, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h2384, h2475, hlam]
                              · linarith only [h2474, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2431, h2466, h2473, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                          · linarith only [h2471, h2472, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2471, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2387, h2466, h2470, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2469, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2466, h2468, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2467, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2486 | h2486
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2487 | h2487
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2488 | h2488
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2489 | h2489
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2490 | h2490
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2491 | h2491
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2492 | h2492
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h2493 | h2493
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h2494 | h2494
                                · linarith only [h2494, hc04, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h2384, h2494, hlam]
                              · linarith only [h2493, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2492, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2490, h2491, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2490, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2387, h2489, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h2488, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2487, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h2486, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2465, hlam, p0_0]
    · linarith only [h2384, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2507 | h2507
    · rcases p0_3 (m.d 1 6) (by simp) with h2508 | h2508
      · rcases p0_3 (m.d 2 6) (by simp) with h2509 | h2509
        · linarith only [h2509, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2511 | h2511
          · rcases p0_3 (m.d 4 6) (by simp) with h2512 | h2512
            · rcases p0_3 (m.d 5 6) (by simp) with h2513 | h2513
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2514 | h2514
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2515 | h2515
                  · linarith only [h2508, h2515, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2515, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2514, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2519 | h2519
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2520 | h2520
                  · linarith only [h2508, h2520, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2520, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2519, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2512, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2525 | h2525
            · rcases p0_3 (m.d 5 6) (by simp) with h2526 | h2526
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2527 | h2527
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2528 | h2528
                  · linarith only [h2508, h2528, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2528, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2527, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2532 | h2532
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2533 | h2533
                  · linarith only [h2508, h2533, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2533, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2532, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2525, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2538 | h2538
        · linarith only [h2538, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2540 | h2540
          · rcases p0_3 (m.d 4 6) (by simp) with h2541 | h2541
            · rcases p0_3 (m.d 5 6) (by simp) with h2542 | h2542
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2543 | h2543
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2544 | h2544
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2545 | h2545
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2546 | h2546
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2547 | h2547
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2548 | h2548
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2549 | h2549
                            · linarith only [h2540, h2549, hc03, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2549, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2547, h2548, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2547, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2507, h2546, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2545, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2508, h2542, h2544, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2543, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2558 | h2558
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2559 | h2559
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2560 | h2560
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2561 | h2561
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2562 | h2562
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2563 | h2563
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2564 | h2564
                            · linarith only [h2508, h2540, h2564, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2564, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2562, h2563, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2562, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2507, h2561, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2560, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2559, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2558, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2541, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2574 | h2574
            · rcases p0_3 (m.d 5 6) (by simp) with h2575 | h2575
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2576 | h2576
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2577 | h2577
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2578 | h2578
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2579 | h2579
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2580 | h2580
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2581 | h2581
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2582 | h2582
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h2583 | h2583
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h2584 | h2584
                                · linarith only [h2584, hc04, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h2507, h2584, hlam]
                              · linarith only [h2583, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2582, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2580, h2581, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2580, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2507, h2579, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2578, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2508, h2575, h2577, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2576, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2595 | h2595
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2596 | h2596
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2597 | h2597
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2598 | h2598
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2599 | h2599
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2600 | h2600
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2601 | h2601
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h2602 | h2602
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h2603 | h2603
                                · linarith only [h2508, h2603, hc04, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h2507, h2603, hlam]
                              · linarith only [h2602, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2601, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2599, h2600, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2599, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2507, h2598, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2597, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2596, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2595, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2574, hlam, p0_0]
    · linarith only [h2507, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2616 | h2616
    · rcases p0_3 (m.d 1 6) (by simp) with h2617 | h2617
      · rcases p0_3 (m.d 2 6) (by simp) with h2618 | h2618
        · rcases p0_3 (m.d 3 6) (by simp) with h2619 | h2619
          · linarith only [h2619, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2621 | h2621
            · rcases p0_3 (m.d 5 6) (by simp) with h2622 | h2622
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2623 | h2623
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2624 | h2624
                  · linarith only [h2617, h2624, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2624, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2623, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2628 | h2628
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2629 | h2629
                  · linarith only [h2617, h2629, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2629, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2628, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2621, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2634 | h2634
          · linarith only [h2634, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2636 | h2636
            · rcases p0_3 (m.d 5 6) (by simp) with h2637 | h2637
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2638 | h2638
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2639 | h2639
                  · linarith only [h2617, h2639, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2639, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2638, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2643 | h2643
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2644 | h2644
                  · linarith only [h2617, h2644, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2644, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2643, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2636, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2649 | h2649
        · rcases p0_3 (m.d 3 6) (by simp) with h2650 | h2650
          · linarith only [h2650, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2652 | h2652
            · rcases p0_3 (m.d 5 6) (by simp) with h2653 | h2653
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2654 | h2654
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2655 | h2655
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2656 | h2656
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2657 | h2657
                      · linarith only [h2649, h2657, hc02, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2657, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2656, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2616, h2617, h2655, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2654, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2663 | h2663
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2664 | h2664
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2665 | h2665
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2666 | h2666
                      · linarith only [h2617, h2649, h2666, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2666, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2665, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2616, h2617, h2664, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2663, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2652, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2673 | h2673
          · linarith only [h2673, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2675 | h2675
            · rcases p0_3 (m.d 5 6) (by simp) with h2676 | h2676
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2677 | h2677
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2678 | h2678
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2679 | h2679
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2680 | h2680
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2681 | h2681
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2682 | h2682
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2683 | h2683
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h2684 | h2684
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h2685 | h2685
                                · linarith only [h2617, h2685, hc04, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h2616, h2685, hlam]
                              · linarith only [h2684, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2681, h2683, hc34, hc46, hlam, hphi, p0_1]
                          · linarith only [h2681, h2682, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2681, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2649, h2676, h2680, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2679, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2678, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2677, hc12, hlam, hphi, ht01, u0ehi0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2696 | h2696
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2697 | h2697
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2698 | h2698
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2699 | h2699
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2700 | h2700
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2701 | h2701
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2702 | h2702
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h2703 | h2703
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h2704 | h2704
                                · linarith only [h2617, h2704, hc04, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h2616, h2704, hlam]
                              · linarith only [h2703, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2702, hc03, hc46, hlam, hphi, ht34, p0_1]
                          · linarith only [h2700, h2701, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2700, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2699, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2698, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2697, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2696, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2675, hlam, p0_0]
    · linarith only [h2616, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2718 | h2718
    · rcases p0_3 (m.d 1 6) (by simp) with h2719 | h2719
      · rcases p0_3 (m.d 2 6) (by simp) with h2720 | h2720
        · rcases p0_3 (m.d 3 6) (by simp) with h2721 | h2721
          · rcases p0_3 (m.d 4 6) (by simp) with h2722 | h2722
            · rcases p0_3 (m.d 5 6) (by simp) with h2723 | h2723
              · linarith only [h2723, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2725 | h2725
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2726 | h2726
                  · linarith only [h2719, h2726, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2726, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2725, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2722, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2731 | h2731
            · rcases p0_3 (m.d 5 6) (by simp) with h2732 | h2732
              · linarith only [h2732, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2734 | h2734
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2735 | h2735
                  · linarith only [h2719, h2735, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2735, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2734, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2731, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2740 | h2740
          · rcases p0_3 (m.d 4 6) (by simp) with h2741 | h2741
            · rcases p0_3 (m.d 5 6) (by simp) with h2742 | h2742
              · linarith only [h2742, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2744 | h2744
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2745 | h2745
                  · linarith only [h2719, h2745, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2745, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2744, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2741, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2750 | h2750
            · rcases p0_3 (m.d 5 6) (by simp) with h2751 | h2751
              · linarith only [h2751, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2753 | h2753
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2754 | h2754
                  · linarith only [h2719, h2754, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2754, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2753, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2750, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2759 | h2759
        · rcases p0_3 (m.d 3 6) (by simp) with h2760 | h2760
          · rcases p0_3 (m.d 4 6) (by simp) with h2761 | h2761
            · rcases p0_3 (m.d 5 6) (by simp) with h2762 | h2762
              · linarith only [h2762, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2764 | h2764
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2765 | h2765
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2766 | h2766
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2767 | h2767
                      · linarith only [h2759, h2767, hc02, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2767, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2766, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2718, h2719, h2765, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2764, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2761, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2774 | h2774
            · rcases p0_3 (m.d 5 6) (by simp) with h2775 | h2775
              · linarith only [h2775, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2777 | h2777
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2778 | h2778
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2779 | h2779
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2780 | h2780
                      · linarith only [h2719, h2759, h2780, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2780, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2779, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2718, h2719, h2778, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2777, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2774, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2787 | h2787
          · rcases p0_3 (m.d 4 6) (by simp) with h2788 | h2788
            · rcases p0_3 (m.d 5 6) (by simp) with h2789 | h2789
              · linarith only [h2789, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2791 | h2791
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2792 | h2792
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2793 | h2793
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2794 | h2794
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2795 | h2795
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2796 | h2796
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2797 | h2797
                            · linarith only [h2719, h2787, h2797, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2797, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2795, h2796, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2795, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2718, h2759, h2794, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2793, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2792, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2791, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2788, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2807 | h2807
            · rcases p0_3 (m.d 5 6) (by simp) with h2808 | h2808
              · linarith only [h2808, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2810 | h2810
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2811 | h2811
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2812 | h2812
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2813 | h2813
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2814 | h2814
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2815 | h2815
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2816 | h2816
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h2817 | h2817
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h2818 | h2818
                                · linarith only [h2759, h2818, hc04, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h2718, h2818, hlam]
                              · linarith only [h2817, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2787, h2816, hc03, hc46, hlam, hphi, ht34, p0_1]
                          · linarith only [h2814, h2815, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2814, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2813, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2812, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2718, h2719, h2811, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2810, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h2807, hlam, p0_0]
    · linarith only [h2718, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2832 | h2832
    · rcases p0_3 (m.d 1 6) (by simp) with h2833 | h2833
      · linarith only [h2833, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2835 | h2835
        · rcases p0_3 (m.d 3 6) (by simp) with h2836 | h2836
          · rcases p0_3 (m.d 4 6) (by simp) with h2837 | h2837
            · rcases p0_3 (m.d 5 6) (by simp) with h2838 | h2838
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2839 | h2839
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2840 | h2840
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2841 | h2841
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2842 | h2842
                      · linarith only [h2835, h2842, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2842, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2841, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2832, h2840, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2839, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2838, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2849 | h2849
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2850 | h2850
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2851 | h2851
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2852 | h2852
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2853 | h2853
                      · linarith only [h2835, h2853, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2853, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2852, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2832, h2851, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2850, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2849, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2860 | h2860
            · rcases p0_3 (m.d 5 6) (by simp) with h2861 | h2861
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2862 | h2862
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2863 | h2863
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2864 | h2864
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2865 | h2865
                      · linarith only [h2835, h2865, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2865, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2864, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2832, h2863, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2862, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2861, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2872 | h2872
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2873 | h2873
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2874 | h2874
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2875 | h2875
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2876 | h2876
                      · linarith only [h2835, h2876, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h2876, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2875, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2832, h2874, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2873, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2872, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2883 | h2883
          · rcases p0_3 (m.d 4 6) (by simp) with h2884 | h2884
            · rcases p0_3 (m.d 5 6) (by simp) with h2885 | h2885
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2886 | h2886
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2887 | h2887
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2888 | h2888
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2889 | h2889
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2890 | h2890
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2891 | h2891
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2892 | h2892
                            · linarith only [h2883, h2892, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2892, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2890, h2891, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2890, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2832, h2835, h2889, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2888, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2887, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2886, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2885, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2902 | h2902
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2903 | h2903
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2904 | h2904
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2905 | h2905
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2906 | h2906
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2907 | h2907
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2908 | h2908
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2909 | h2909
                            · linarith only [h2883, h2909, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h2909, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h2907, h2908, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2907, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2832, h2835, h2906, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2905, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2904, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2903, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2902, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2919 | h2919
            · rcases p0_3 (m.d 5 6) (by simp) with h2920 | h2920
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2921 | h2921
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2922 | h2922
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2923 | h2923
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2924 | h2924
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2925 | h2925
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2926 | h2926
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2927 | h2927
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h2928 | h2928
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h2929 | h2929
                                · linarith only [h2919, h2929, hc04, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h2929, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                              · linarith only [h2928, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2832, h2883, h2927, hc03, hc06, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2925, h2926, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2925, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2832, h2835, h2924, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2923, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2922, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2921, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2920, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2941 | h2941
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2942 | h2942
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2943 | h2943
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h2944 | h2944
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2945 | h2945
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h2946 | h2946
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h2947 | h2947
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h2948 | h2948
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h2949 | h2949
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h2950 | h2950
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h2951 | h2951
                                  · linarith only [h2951, hc05, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                  · linarith only [h2832, h2951, hlam]
                                · linarith only [h2919, h2950, hc04, hc56, hlam, hphi, ht45, p0_1]
                              · linarith only [h2949, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2832, h2883, h2948, hc03, hc06, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2946, h2947, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h2946, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2835, h2945, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2944, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2943, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2942, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2941, hlam, p0_0]
    · linarith only [h2832, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2965 | h2965
    · rcases p0_3 (m.d 1 6) (by simp) with h2966 | h2966
      · rcases p0_3 (m.d 2 6) (by simp) with h2967 | h2967
        · linarith only [h2967, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2969 | h2969
          · rcases p0_3 (m.d 4 6) (by simp) with h2970 | h2970
            · rcases p0_3 (m.d 5 6) (by simp) with h2971 | h2971
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2972 | h2972
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2973 | h2973
                  · linarith only [h2966, h2973, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2973, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2972, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2971, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2978 | h2978
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2979 | h2979
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2980 | h2980
                  · linarith only [h2966, h2980, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2980, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2979, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2978, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2985 | h2985
            · rcases p0_3 (m.d 5 6) (by simp) with h2986 | h2986
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2987 | h2987
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2988 | h2988
                  · linarith only [h2966, h2988, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2988, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2987, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2986, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2993 | h2993
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2994 | h2994
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2995 | h2995
                  · linarith only [h2966, h2995, hc01, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h2995, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h2994, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h2993, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h3000 | h3000
        · linarith only [h3000, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h3002 | h3002
          · rcases p0_3 (m.d 4 6) (by simp) with h3003 | h3003
            · rcases p0_3 (m.d 5 6) (by simp) with h3004 | h3004
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3005 | h3005
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3006 | h3006
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3007 | h3007
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3008 | h3008
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h3009 | h3009
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h3010 | h3010
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h3011 | h3011
                            · linarith only [h3002, h3011, hc03, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h3011, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h3009, h3010, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h3009, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2965, h3008, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h3007, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h2966, h3006, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3005, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3004, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3021 | h3021
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3022 | h3022
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3023 | h3023
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3024 | h3024
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3025 | h3025
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h3026 | h3026
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h3027 | h3027
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h3028 | h3028
                            · linarith only [h2966, h3002, h3028, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h3028, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h3026, h3027, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h3026, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2965, h3025, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h3024, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3023, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3022, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3021, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h3038 | h3038
            · rcases p0_3 (m.d 5 6) (by simp) with h3039 | h3039
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3040 | h3040
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3041 | h3041
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3042 | h3042
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3043 | h3043
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h3044 | h3044
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h3045 | h3045
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h3046 | h3046
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h3047 | h3047
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h3048 | h3048
                                · linarith only [h3038, h3048, hc04, hc26, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h3048, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                              · linarith only [h3047, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2965, h3002, h3046, hc03, hc06, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h3044, h3045, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h3044, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h2965, h3043, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h3042, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3041, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3040, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3039, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3060 | h3060
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3061 | h3061
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3062 | h3062
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3063 | h3063
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3064 | h3064
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h3065 | h3065
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h3066 | h3066
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h3067 | h3067
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h3068 | h3068
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h3069 | h3069
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h3070 | h3070
                                  · linarith only [h2966, h3070, hc05, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                  · linarith only [h2965, h3070, hlam]
                                · linarith only [h2965, h3038, h3069, hc04, hc06, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h3068, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h2965, h3002, h3065, h3067, hc06, hlam, hphi, p0_1, u0ehi3]
                          · linarith only [h3065, h3066, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h3065, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h3064, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3063, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3062, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3061, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3060, hlam, p0_0]
    · linarith only [h2965, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h3084 | h3084
    · rcases p0_3 (m.d 1 6) (by simp) with h3085 | h3085
      · rcases p0_3 (m.d 2 6) (by simp) with h3086 | h3086
        · rcases p0_3 (m.d 3 6) (by simp) with h3087 | h3087
          · linarith only [h3087, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h3089 | h3089
            · rcases p0_3 (m.d 5 6) (by simp) with h3090 | h3090
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3091 | h3091
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3092 | h3092
                  · linarith only [h3085, h3092, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h3092, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3091, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3090, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3097 | h3097
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3098 | h3098
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3099 | h3099
                  · linarith only [h3085, h3099, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h3099, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3098, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3097, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h3104 | h3104
          · linarith only [h3104, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h3106 | h3106
            · rcases p0_3 (m.d 5 6) (by simp) with h3107 | h3107
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3108 | h3108
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3109 | h3109
                  · linarith only [h3085, h3109, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h3109, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3108, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3107, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3114 | h3114
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3115 | h3115
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3116 | h3116
                  · linarith only [h3085, h3116, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h3116, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3115, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3114, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h3121 | h3121
        · rcases p0_3 (m.d 3 6) (by simp) with h3122 | h3122
          · linarith only [h3122, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h3124 | h3124
            · rcases p0_3 (m.d 5 6) (by simp) with h3125 | h3125
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3126 | h3126
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3127 | h3127
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3128 | h3128
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3129 | h3129
                      · linarith only [h3121, h3129, hc02, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h3129, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h3128, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3084, h3085, h3127, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h3126, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3125, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3136 | h3136
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3137 | h3137
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3138 | h3138
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3139 | h3139
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3140 | h3140
                      · linarith only [h3085, h3121, h3140, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h3140, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h3139, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3084, h3085, h3138, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h3137, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3136, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h3147 | h3147
          · linarith only [h3147, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h3149 | h3149
            · rcases p0_3 (m.d 5 6) (by simp) with h3150 | h3150
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3151 | h3151
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3152 | h3152
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3153 | h3153
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3154 | h3154
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h3155 | h3155
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h3156 | h3156
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h3157 | h3157
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h3158 | h3158
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h3159 | h3159
                                · linarith only [h3085, h3149, h3159, hc04, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                · linarith only [h3159, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                              · linarith only [h3158, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h3157, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                          · linarith only [h3155, h3156, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h3155, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h3121, h3154, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3153, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3085, h3152, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3151, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3150, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3171 | h3171
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3172 | h3172
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3173 | h3173
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3174 | h3174
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3175 | h3175
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h3176 | h3176
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h3177 | h3177
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h3178 | h3178
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h3179 | h3179
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h3180 | h3180
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h3181 | h3181
                                  · linarith only [h3085, h3181, hc05, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                  · linarith only [h3084, h3181, hlam]
                                · linarith only [h3149, h3179, h3180, hc45, hc56, hlam, hphi, p0_1]
                              · linarith only [h3179, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h3178, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                          · linarith only [h3176, h3177, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h3176, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h3121, h3175, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3174, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3173, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3172, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3171, hlam, p0_0]
    · linarith only [h3084, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h3195 | h3195
    · rcases p0_3 (m.d 1 6) (by simp) with h3196 | h3196
      · rcases p0_3 (m.d 2 6) (by simp) with h3197 | h3197
        · rcases p0_3 (m.d 3 6) (by simp) with h3198 | h3198
          · rcases p0_3 (m.d 4 6) (by simp) with h3199 | h3199
            · linarith only [h3199, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3201 | h3201
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3202 | h3202
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3203 | h3203
                  · linarith only [h3196, h3203, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h3203, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3202, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3201, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h3208 | h3208
            · linarith only [h3208, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3210 | h3210
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3211 | h3211
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3212 | h3212
                  · linarith only [h3196, h3212, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h3212, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3211, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3210, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h3217 | h3217
          · rcases p0_3 (m.d 4 6) (by simp) with h3218 | h3218
            · linarith only [h3218, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3220 | h3220
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3221 | h3221
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3222 | h3222
                  · linarith only [h3196, h3222, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h3222, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3221, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3220, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h3227 | h3227
            · linarith only [h3227, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3229 | h3229
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3230 | h3230
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3231 | h3231
                  · linarith only [h3196, h3231, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                  · linarith only [h3231, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3230, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3229, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h3236 | h3236
        · rcases p0_3 (m.d 3 6) (by simp) with h3237 | h3237
          · rcases p0_3 (m.d 4 6) (by simp) with h3238 | h3238
            · linarith only [h3238, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3240 | h3240
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3241 | h3241
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3242 | h3242
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3243 | h3243
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3244 | h3244
                      · linarith only [h3236, h3244, hc02, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h3244, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h3243, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3195, h3196, h3242, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h3241, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3240, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h3251 | h3251
            · linarith only [h3251, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3253 | h3253
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3254 | h3254
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3255 | h3255
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3256 | h3256
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3257 | h3257
                      · linarith only [h3196, h3236, h3257, hc02, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                      · linarith only [h3257, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h3256, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3195, h3196, h3255, hc01, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h3254, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3253, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h3264 | h3264
          · rcases p0_3 (m.d 4 6) (by simp) with h3265 | h3265
            · linarith only [h3265, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3267 | h3267
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3268 | h3268
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3269 | h3269
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3270 | h3270
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3271 | h3271
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h3272 | h3272
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h3273 | h3273
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h3274 | h3274
                            · linarith only [h3196, h3264, h3274, hc03, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                            · linarith only [h3274, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h3272, h3273, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h3272, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h3195, h3236, h3271, hc02, hc06, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h3270, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3269, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3268, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3267, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h3284 | h3284
            · linarith only [h3284, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h3286 | h3286
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3287 | h3287
                · rcases m.htr 0 1 6 (by decide) (by decide) with h3288 | h3288
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h3289 | h3289
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3290 | h3290
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h3291 | h3291
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h3292 | h3292
                          · rcases m.htr 0 3 6 (by decide) (by decide) with h3293 | h3293
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h3294 | h3294
                              · rcases m.htr 0 4 6 (by decide) (by decide) with h3295 | h3295
                                · rcases m.htr 0 5 6 (by decide) (by decide) with h3296 | h3296
                                  · linarith only [h3196, h3296, hc05, hc16, hlam, hphi, ht0b, ht6b, p0_1]
                                  · linarith only [h3195, h3296, hlam]
                                · linarith only [h3195, h3295, hc04, hc06, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h3294, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h3195, h3264, h3291, h3293, hc06, hlam, hphi, p0_1, u0ehi3]
                          · linarith only [h3291, h3292, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h3291, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h3290, hc26, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h3289, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · linarith only [h3288, hc16, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3287, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3286, hlam, p0_0]
    · linarith only [h3195, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

end R2N4
