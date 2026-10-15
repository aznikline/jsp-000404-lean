import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_13_24_L_I_H_R (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                      · linarith only [h11, h7, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                          · linarith only [h0, h11, h14, h3, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h14, hc45, hlam, hphi, u4ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                          · linarith only [h0, h11, h17, h3, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h17, hc45, hlam, hphi, u4ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                      · linarith only [h1, h20, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h10, h22, h7, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                          · linarith only [h2, h24, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h24, hc45, hlam, hphi, u4ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h27, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                      · linarith only [h1, h30, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                          · linarith only [h2, h33, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h33, hc45, hlam, hphi, u4ehi1]
                        · linarith only [h29, h32, h7, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                      · linarith only [h1, h37, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                          · linarith only [h2, h40, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h40, hc45, hlam, hphi, u4ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
                          · linarith only [h2, h43, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h43, hc45, hlam, hphi, u4ehi1]
              · linarith only [h6, hc45, hlam, hphi, u4ehi0]
            · linarith only [h4, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h48 | h48
            · rcases m.htr 0 4 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                  · linarith only [h0, h51, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                      · linarith only [h1, h54, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                          · linarith only [h2, h57, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h4, h48, h49, h57, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                        · linarith only [h4, h48, h56, hc13, hc34, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                      · linarith only [h4, h48, h49, h61, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                        · linarith only [h50, h53, h63, hlam]
                        · linarith only [h4, h48, h63, hc13, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
                  · linarith only [h3, h4, h50, h66, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h69 | h69
                      · linarith only [h3, h4, h50, h68, h69, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                          · linarith only [h2, h72, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h4, h48, h49, h72, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                        · linarith only [h4, h48, h71, hc13, hc34, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                      · linarith only [h4, h48, h49, h76, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                          · linarith only [h2, h79, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h79, hc45, hlam, hphi, u4ehi1]
                        · linarith only [h4, h48, h78, hc13, hc34, hlam, hphi]
              · linarith only [h49, hc45, hlam, hphi, u4ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h84 | h84
              · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
                · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                  · linarith only [h0, h86, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                      · linarith only [h4, h84, h89, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                        · linarith only [h1, h48, h91, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                          · linarith only [h2, h93, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h4, h84, h93, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                      · linarith only [h1, h4, h48, h96, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h1, h48, h98, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
                          · linarith only [h100, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h100, h84, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                  · linarith only [h103, h3, h48, h85, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                      · linarith only [h106, h3, h4, h48, h85, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                        · linarith only [h105, h106, h108, h3, h48, h85, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h105, h108, h85, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                      · linarith only [h111, h4, h84, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                        · linarith only [h113, h3, h48, h85, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                          · linarith only [h115, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h115, h4, h84, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h84, hc45, hlam, hphi, u4ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h119 | h119
          · rcases m.htr 0 3 5 (by decide) (by decide) with h120 | h120
            · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
              · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                · linarith only [h0, h122, h3, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                  · linarith only [h0, h124, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                      · linarith only [h1, h127, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                          · linarith only [h130, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h119, h121, h130, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h122, h126, h129, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                      · linarith only [h1, h134, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                          · linarith only [h137, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h137, hc45, hlam, hphi, u4ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                          · linarith only [h140, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h140, hc45, hlam, hphi, u4ehi1]
              · linarith only [h121, hc45, hlam, hphi, u4ehi0]
            · linarith only [h119, h120, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h145 | h145
            · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
              · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
                · linarith only [h0, h147, h3, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
                  · linarith only [h0, h149, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h151 | h151
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                      · linarith only [h1, h119, h152, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                          · linarith only [h155, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h146, h155, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h119, h145, h147, h154, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h159 | h159
                      · linarith only [h119, h145, h146, h159, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h161 | h161
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                          · linarith only [h162, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h119, h145, h146, h162, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                        · linarith only [h119, h145, h161, hc13, hc34, hlam, hphi]
              · linarith only [h146, hc45, hlam, hphi, u4ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
              · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                · linarith only [h0, h168, h3, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
                  · linarith only [h0, h170, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                      · linarith only [h1, h119, h173, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
                        · linarith only [h1, h145, h175, hlam]
                        · linarith only [h168, h172, h175, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h178 | h178
                      · linarith only [h119, h167, h178, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h180 | h180
                        · linarith only [h1, h145, h180, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                          · linarith only [h182, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h167, h182, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h167, hc45, hlam, hphi, u4ehi0]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h186 | h186
        · rcases m.htr 0 3 4 (by decide) (by decide) with h187 | h187
          · linarith only [h0, h186, h187, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h189 | h189
            · rcases m.htr 0 4 5 (by decide) (by decide) with h190 | h190
              · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                  · linarith only [h0, h192, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                      · linarith only [h0, h187, h191, h192, h195, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h0, h191, h195, h2, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                      · linarith only [h0, h191, h198, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h191, h198, h2, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
                  · linarith only [h0, h186, h191, h2, h201, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h186, h191, h2, h201, hc12, hc24, hlam, hphi]
              · linarith only [h190, hc45, hlam, hphi, u4ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h205 | h205
              · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
                · rcases m.htr 1 2 4 (by decide) (by decide) with h207 | h207
                  · linarith only [h0, h2, h207, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
                      · linarith only [h187, h205, h210, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h2, h206, h210, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h213 | h213
                      · linarith only [h0, h187, h205, h206, h213, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h2, h206, h213, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h216 | h216
                  · linarith only [h0, h186, h2, h206, h216, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h186, h2, h206, h216, hc12, hc24, hlam, hphi]
              · linarith only [h205, hc45, hlam, hphi, u4ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h220 | h220
          · linarith only [h1, h2, h220, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h222 | h222
            · rcases m.htr 0 4 5 (by decide) (by decide) with h223 | h223
              · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                · linarith only [h0, h186, h2, h224, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h226 | h226
                  · linarith only [h0, h2, h226, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                      · linarith only [h220, h222, h223, h229, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h1, h2, h224, h228, h229, h232, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h1, h2, h223, h224, h232, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h2, h222, h224, h228, h231, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                      · linarith only [h1, h2, h220, h226, h236, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h238 | h238
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
                          · linarith only [h1, h2, h236, h238, h239, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h1, h2, h223, h239, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1, h2, h222, h236, h238, hc13, hc34, hlam, hphi]
              · linarith only [h223, hc45, hlam, hphi, u4ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h244 | h244
              · rcases m.htr 1 2 3 (by decide) (by decide) with h245 | h245
                · linarith only [h0, h186, h2, h220, h244, h245, hc02, hc14, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h247 | h247
                  · linarith only [h0, h2, h247, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h249 | h249
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                      · linarith only [h1, h2, h220, h244, h247, h250, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h252 | h252
                        · linarith only [h1, h2, h222, h250, h252, hc03, hc34, hlam, hphi]
                        · linarith only [h245, h249, h252, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h255 | h255
                      · linarith only [h1, h255, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
                        · linarith only [h1, h2, h222, h244, h255, h257, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h260 | h260
                            · linarith only [h0, h2, h255, h260, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h262 | h262
                              · linarith only [h222, h244, h260, h262, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h264 | h264
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h265 | h265
                                  · rcases h3bigk with h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h186, h245, h262, h265, hc12, hc34, hlam, hphi, ht23, p266_1]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h186, hlam, p266_1]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h220, hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h222, hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h1, hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h245, hlam, p266_1]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h255, hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h257, hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h262, h265, hc03, hc34, hlam, hphi, p266_1]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h245, h262, h265, hc12, hc34, hlam, hphi, ht23, p266_1]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h260, hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h262, hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      rcases p266_3 (m.d 0 3) (by simp) with h282 | h282
                                      · linarith only [h282, hlam, p266_0]
                                      · rcases p266_3 (m.d 1 3) (by simp) with h284 | h284
                                        · linarith only [h255, h284, hlam]
                                        · rcases p266_3 (m.d 2 3) (by simp) with h286 | h286
                                          · linarith only [h260, h286, hlam]
                                          · linarith only [h186, h286, hlam]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      rcases p266_3 (m.d 0 3) (by simp) with h289 | h289
                                      · linarith only [h220, h289, hlam]
                                      · linarith only [h1, h289, hlam]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h0, h186, hc12, hc34, hlam, hphi, ht23, p266_1]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h1, h222, h245, hc12, hc34, hlam, hphi, ht23, p266_1]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      rcases p266_3 (m.d 0 3) (by simp) with h295 | h295
                                      · linarith only [h295, hlam, p266_0]
                                      · rcases p266_3 (m.d 1 3) (by simp) with h297 | h297
                                        · linarith only [h257, h297, hlam]
                                        · rcases p266_3 (m.d 2 3) (by simp) with h299 | h299
                                          · linarith only [h262, h299, hlam]
                                          · linarith only [h186, h299, hlam]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      rcases p266_3 (m.d 0 3) (by simp) with h302 | h302
                                      · linarith only [h222, h302, hlam]
                                      · linarith only [h1, h302, hlam]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h0, h186, hc12, hc35, hlam, hphi, ht23, p266_1]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [h265, hlam, p266_0]
                                    · have p266_0 := h266c.1
                                      have p266_1 := h266c.2.1
                                      have p266_2 := h266c.2.2.1
                                      have p266_3 := h266c.2.2.2
                                      linarith only [hlam, p266_0]
                                  · linarith only [h244, h247, h260, h265, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                · linarith only [h2, h244, h247, h264, hlam]
                          · linarith only [h2, h244, h259, hlam]
              · linarith only [h244, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h312 | h312
      · linarith only [h1, h312, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h314 | h314
        · linarith only [h0, h1, h314, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h316 | h316
          · rcases m.htr 0 3 5 (by decide) (by decide) with h317 | h317
            · rcases m.htr 0 4 5 (by decide) (by decide) with h318 | h318
              · rcases m.htr 1 2 3 (by decide) (by decide) with h319 | h319
                · linarith only [h0, h1, h314, h319, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h321 | h321
                  · linarith only [h0, h1, h319, h321, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h323 | h323
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h324 | h324
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h325 | h325
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h326 | h326
                          · linarith only [h0, h312, h319, h323, h324, h326, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h312, h316, h318, h326, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h0, h1, h323, h325, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h316, h318, h324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h335 | h335
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                                  · linarith only [h316, h337, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h318, h337, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h336, hc45, hlam, hphi, u4ehi2]
                              · linarith only [h1, h316, h318, h319, h323, h332, h335, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h1, h316, h318, h319, h334, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h316, h318, h333, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h1, h317, h332, hlam]
                      · linarith only [h1, h316, h331, hlam]
              · linarith only [h318, hc45, hlam, hphi, u4ehi0]
            · linarith only [h316, h317, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h348 | h348
            · rcases m.htr 0 4 5 (by decide) (by decide) with h349 | h349
              · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
                · linarith only [h0, h314, h350, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h352 | h352
                  · linarith only [h0, h1, h316, h352, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h354 | h354
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                      · linarith only [h0, h1, h316, h350, h355, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h354, h355, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h358 | h358
                      · linarith only [h316, h348, h349, h358, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h1, h358, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h349, hc45, hlam, hphi, u4ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h362 | h362
              · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                · linarith only [h0, h1, h348, h363, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                  · linarith only [h0, h1, h348, h365, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                      · linarith only [h0, h1, h316, h363, h368, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h367, h368, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                      · linarith only [h316, h362, h371, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h1, h371, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h362, hc45, hlam, hphi, u4ehi0]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h375 | h375
    · rcases m.htr 0 1 4 (by decide) (by decide) with h376 | h376
      · linarith only [h0, h376, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h378 | h378
        · rcases m.htr 0 3 4 (by decide) (by decide) with h379 | h379
          · linarith only [h0, h375, h379, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h381 | h381
            · rcases m.htr 0 4 5 (by decide) (by decide) with h382 | h382
              · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
                · rcases m.htr 1 2 4 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h386 | h386
                      · linarith only [h375, h376, h379, h384, h386, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h388 | h388
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h389 | h389
                          · linarith only [h375, h376, h386, h388, h389, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h375, h376, h382, h389, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · linarith only [h375, h376, h381, h383, h386, h388, hc23, hc34, hlam, hphi]
                    · linarith only [h384, h385, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h375, h381, h382, h384, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h0, h375, h381, h382, h383, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h382, hc45, hlam, hphi, u4ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h397 | h397
              · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h400 | h400
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                      · linarith only [h375, h376, h399, h401, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h403 | h403
                        · linarith only [h375, h376, h381, h397, h401, h403, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h405 | h405
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h406 | h406
                            · linarith only [h376, h397, h401, h406, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h408 | h408
                              · linarith only [h375, h381, h397, h398, h408, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h410 | h410
                                · linarith only [h399, h410, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h397, h410, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h376, h397, h405, hlam]
                    · linarith only [h399, h400, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h415 | h415
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h416 | h416
                      · linarith only [h375, h416, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                        · linarith only [h0, h375, h381, h397, h399, h418, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                            · linarith only [h0, h375, h376, h397, h398, h399, h416, h421, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h375, h398, h399, h421, hc23, hc34, hlam, hphi]
                          · linarith only [h376, h397, h420, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h425 | h425
                      · linarith only [h0, h375, h399, h425, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h427 | h427
                        · linarith only [h0, h375, h399, h427, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h429 | h429
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                            · linarith only [h0, h375, h376, h397, h398, h399, h425, h430, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h375, h398, h399, h430, hc23, hc34, hlam, hphi]
                          · linarith only [h376, h397, h429, hlam]
                · linarith only [h0, h378, h398, hlam]
              · linarith only [h397, hc45, hlam, hphi, u4ehi0]
        · linarith only [h0, h375, h378, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h437 | h437
      · linarith only [h0, h437, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h439 | h439
        · rcases m.htr 0 3 4 (by decide) (by decide) with h440 | h440
          · rcases m.htr 0 3 5 (by decide) (by decide) with h441 | h441
            · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
              · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                · rcases m.htr 1 2 4 (by decide) (by decide) with h444 | h444
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h445 | h445
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h446 | h446
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h447 | h447
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h448 | h448
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h449 | h449
                            · linarith only [h439, h449, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                                · linarith only [h375, h440, h443, h449, h452, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h442, h452, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h455 | h455
                                · linarith only [h444, h455, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h455, hc45, hlam, hphi, u4ehi2]
                          · linarith only [h437, h442, h448, hlam]
                        · linarith only [h375, h440, h441, h447, hc05, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h375, h440, h442, h446, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h375, h440, h442, h443, h445, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h375, h440, h442, h443, h444, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h0, h439, h443, hlam]
              · linarith only [h442, hc45, hlam, hphi, u4ehi0]
            · linarith only [h440, h441, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h466 | h466
            · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
              · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
                      · linarith only [h440, h467, h468, h471, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h475 | h475
                            · linarith only [h439, h475, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h477 | h477
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                                · linarith only [h469, h478, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h478, hc45, hlam, hphi, u4ehi2]
                              · linarith only [h375, h466, h471, h477, hc23, hc34, hlam, hphi]
                          · linarith only [h375, h437, h466, h467, h471, h474, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                        · linarith only [h375, h466, h473, hlam]
                    · linarith only [h469, h470, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h485 | h485
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h486 | h486
                      · linarith only [h440, h467, h486, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h488 | h488
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                            · linarith only [h375, h466, h467, h486, h490, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h492 | h492
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h493 | h493
                                · linarith only [h0, h439, h469, h490, h492, h493, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                                · linarith only [h0, h439, h467, h469, h493, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h0, h439, h466, h469, h490, h492, hc23, hc34, hlam, hphi]
                          · linarith only [h437, h467, h489, hlam]
                        · linarith only [h375, h466, h488, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h499 | h499
                      · linarith only [h440, h466, h467, h499, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h501 | h501
                        · linarith only [h468, h485, h501, hlam]
                        · linarith only [h375, h466, h501, hlam]
                · linarith only [h0, h439, h468, hlam]
              · linarith only [h467, hc45, hlam, hphi, u4ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h506 | h506
              · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
                · rcases m.htr 1 2 4 (by decide) (by decide) with h508 | h508
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h509 | h509
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h510 | h510
                      · linarith only [h440, h506, h510, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h512 | h512
                        · linarith only [h466, h510, h512, hc03, hc34, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h514 | h514
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h515 | h515
                            · linarith only [h437, h506, h510, h515, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h517 | h517
                              · linarith only [h375, h512, h517, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h519 | h519
                                · linarith only [h508, h519, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h437, h506, h510, h519, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                          · linarith only [h437, h506, h514, hlam]
                    · linarith only [h508, h509, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h524 | h524
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h525 | h525
                      · linarith only [h440, h506, h525, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
                        · linarith only [h466, h525, h527, hc03, hc34, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
                            · linarith only [h437, h439, h506, h525, h530, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h532 | h532
                              · linarith only [h0, h375, h439, h508, h527, h530, h532, hc03, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h534 | h534
                                · linarith only [h508, h524, h530, h534, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                                · linarith only [h437, h506, h534, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h437, h506, h529, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h538 | h538
                      · linarith only [h440, h506, h538, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h540 | h540
                        · linarith only [h375, h466, h507, h524, h540, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h542 | h542
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h543 | h543
                            · linarith only [h375, h538, h543, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h545 | h545
                              · linarith only [h375, h437, h439, h506, h508, h540, h543, h545, hc01, hc02, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h547 | h547
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h548 | h548
                                  · rcases h3bigk with h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h375, hlam, p549_1]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h0, h439, h524, h543, h547, hc23, hc34, hlam, hphi, p549_1]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h440, hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h466, hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h507, h524, h543, h547, hc03, hc34, hlam, hphi, p549_1]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h507, h524, h543, h547, hc23, hc34, hlam, hphi, p549_1]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h538, hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h540, hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h439, hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h507, hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h543, hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h545, hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      rcases p549_3 (m.d 0 3) (by simp) with h565 | h565
                                      · linarith only [h565, hlam, p549_0]
                                      · rcases p549_3 (m.d 1 3) (by simp) with h567 | h567
                                        · linarith only [h538, h567, hlam]
                                        · linarith only [h375, h567, hlam]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h375, hc01, hc34, hlam, hphi, ht12, ht23, p549_1]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      rcases p549_3 (m.d 0 3) (by simp) with h571 | h571
                                      · linarith only [h440, h571, hlam]
                                      · linarith only [h439, h571, hlam]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h0, h524, h545, hc02, hc34, hlam, hphi, ht23, p549_1]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      rcases p549_3 (m.d 0 3) (by simp) with h576 | h576
                                      · linarith only [h576, hlam, p549_0]
                                      · rcases p549_3 (m.d 1 3) (by simp) with h578 | h578
                                        · linarith only [h540, h578, hlam]
                                        · linarith only [h375, h578, hlam]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h375, hc01, hc35, hlam, hphi, ht12, ht23, p549_1]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      rcases p549_3 (m.d 0 3) (by simp) with h582 | h582
                                      · linarith only [h466, h582, hlam]
                                      · linarith only [h439, h582, hlam]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [h548, hlam, p549_0]
                                    · have p549_0 := h549c.1
                                      have p549_1 := h549c.2.1
                                      have p549_2 := h549c.2.2.1
                                      have p549_3 := h549c.2.2.2
                                      linarith only [hlam, p549_0]
                                  · linarith only [h506, h543, h548, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · linarith only [h437, h506, h508, h547, hlam]
                          · linarith only [h437, h506, h542, hlam]
                · linarith only [h0, h439, h507, hlam]
              · linarith only [h506, hc45, hlam, hphi, u4ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h592 | h592
          · rcases m.htr 0 3 5 (by decide) (by decide) with h593 | h593
            · rcases m.htr 0 4 5 (by decide) (by decide) with h594 | h594
              · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
                · linarith only [h439, h592, h594, h595, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h597 | h597
                  · linarith only [h595, h597, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h599 | h599
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h600 | h600
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h601 | h601
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h602 | h602
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h603 | h603
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h604 | h604
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h605 | h605
                                · linarith only [h597, h599, h603, h605, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                · linarith only [h592, h594, h605, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                              · linarith only [h375, h592, h595, h604, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                            · linarith only [h375, h592, h595, h603, hlam]
                          · linarith only [h437, h594, h602, hlam]
                        · linarith only [h375, h592, h594, h601, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h375, h592, h600, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h613 | h613
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h614 | h614
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h615 | h615
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h616 | h616
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h617 | h617
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h618 | h618
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h619 | h619
                                  · linarith only [h592, h619, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h594, h619, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h375, h592, h594, h595, h618, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                              · linarith only [h375, h593, h595, h617, hlam]
                            · linarith only [h375, h592, h594, h595, h616, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h437, h594, h615, hlam]
                        · linarith only [h375, h593, h614, hlam]
                      · linarith only [h375, h592, h613, hlam]
              · linarith only [h594, hc45, hlam, hphi, u4ehi0]
            · linarith only [h592, h593, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h630 | h630
            · rcases m.htr 0 4 5 (by decide) (by decide) with h631 | h631
              · rcases m.htr 1 2 3 (by decide) (by decide) with h632 | h632
                · rcases m.htr 1 2 4 (by decide) (by decide) with h633 | h633
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h634 | h634
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h635 | h635
                      · linarith only [h592, h631, h635, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h637 | h637
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h638 | h638
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h639 | h639
                            · linarith only [h632, h635, h639, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h641 | h641
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
                                · linarith only [h633, h642, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h631, h642, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                              · linarith only [h439, h630, h641, hlam]
                          · linarith only [h437, h439, h630, h631, h632, h635, h638, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                        · linarith only [h439, h630, h632, h637, hlam]
                    · linarith only [h439, h632, h634, hc02, hc25, hlam, hphi]
                  · linarith only [h439, h630, h631, h632, h633, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h650 | h650
                  · linarith only [h632, h650, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h652 | h652
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h653 | h653
                      · linarith only [h592, h630, h631, h653, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h655 | h655
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h656 | h656
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h657 | h657
                            · linarith only [h375, h630, h631, h653, h657, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h632, h657, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h375, h437, h630, h631, h653, h656, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                        · linarith only [h375, h630, h655, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h662 | h662
                      · linarith only [h592, h631, h662, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h664 | h664
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h665 | h665
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h666 | h666
                            · linarith only [h375, h662, h666, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h632, h666, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h437, h631, h665, hlam]
                        · linarith only [h375, h630, h664, hlam]
              · linarith only [h631, hc45, hlam, hphi, u4ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h672 | h672
              · rcases m.htr 1 2 3 (by decide) (by decide) with h673 | h673
                · rcases m.htr 1 2 4 (by decide) (by decide) with h674 | h674
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h675 | h675
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h676 | h676
                      · linarith only [h592, h672, h676, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                        · linarith only [h630, h676, h678, hc03, hc34, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h680 | h680
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h681 | h681
                            · linarith only [h673, h676, h681, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h683 | h683
                              · linarith only [h673, h678, h683, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h685 | h685
                                · linarith only [h674, h685, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h437, h672, h676, h685, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                          · linarith only [h437, h672, h680, hlam]
                    · linarith only [h0, h439, h673, h675, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h439, h673, h674, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h691 | h691
                  · linarith only [h673, h691, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h693 | h693
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h694 | h694
                      · linarith only [h592, h672, h694, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h696 | h696
                        · linarith only [h0, h439, h630, h694, h696, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h673, h693, h696, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h699 | h699
                      · linarith only [h592, h672, h699, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h701 | h701
                        · linarith only [h0, h439, h630, h699, h701, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h703 | h703
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h704 | h704
                            · linarith only [h0, h673, h699, h704, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h673, h704, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h437, h672, h703, hlam]
              · linarith only [h672, hc45, hlam, hphi, u4ehi0]

end R2N4
