import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5354000 in
private theorem n8l_sBT8_M_LI_H_L_s0 (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h6elo := hb6.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 1 6 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 2 6 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 3 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h17 | h17
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h20 | h20
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h21 | h21
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                                            · linarith only [h0, h15, h22, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                            · linarith only [h0, h15, h18, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                          · linarith only [h21, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h20, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h0, h10, h18, h19, h5, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                                      · linarith only [h0, h18, h28, h5, h9, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h30 | h30
                                        · linarith only [h0, h18, h30, h5, h9, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                        · linarith only [h30, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h17, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h15, h16, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                                · linarith only [h0, h15, h35, h5, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h37 | h37
                                  · linarith only [h0, h15, h37, h5, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                  · linarith only [h37, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h14, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h13, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h42 | h42
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h43 | h43
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h46 | h46
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h49 | h49
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h50 | h50
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                                            · linarith only [h0, h44, h51, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                            · linarith only [h1, h47, h51, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                          · linarith only [h50, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h49, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h10, h47, h48, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                                      · linarith only [h0, h47, h5, h57, h9, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h59 | h59
                                        · linarith only [h0, h10, h5, h57, h59, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                        · linarith only [h59, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h46, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h44, h45, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                                · linarith only [h0, h44, h5, h64, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h66 | h66
                                  · linarith only [h0, h44, h5, h66, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                  · linarith only [h66, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h43, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h2, h42, hc14, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h11, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h72 | h72
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h73 | h73
                        · linarith only [h10, h73, h9, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h75 | h75
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h76 | h76
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h79 | h79
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                                      · linarith only [h1, h10, h81, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h83 | h83
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h84 | h84
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                                            · linarith only [h0, h77, h85, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                            · linarith only [h1, h10, h80, h85, hc23, hc35, hlam, hphi]
                                          · linarith only [h76, h81, h84, hc13, hlam, hphi, ht34, ht45, ht56, u6elo0]
                                        · linarith only [h80, h83, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                    · linarith only [h10, h80, h9, hc13, hc35, hlam, hphi]
                                  · linarith only [h79, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h6, h77, h78, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h93 | h93
                                · linarith only [h0, h5, h77, h93, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h95 | h95
                                  · linarith only [h0, h5, h77, h95, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                  · linarith only [h95, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h10, h76, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                          · linarith only [h75, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h72, h9, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h101 | h101
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h102 | h102
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h104 | h104
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h105 | h105
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h108 | h108
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
                                    · linarith only [h1, h109, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h112 | h112
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h113 | h113
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                                            · linarith only [h1, h106, h111, h114, h9, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h116 | h116
                                              · linarith only [h0, h107, h114, h116, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                              · linarith only [h1, h111, h116, h9, hc23, hc34, hlam, hphi]
                                          · linarith only [h113, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h112, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h101, h106, h111, h9, hc23, hc34, hlam, hphi]
                                  · linarith only [h108, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h106, h107, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                                · linarith only [h0, h106, h124, h5, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h126 | h126
                                  · linarith only [h0, h106, h126, h5, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                  · linarith only [h126, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h105, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h104, h9, hc03, hlam, hphi, ht34, ht45, ht56, u6elo4]
                        · linarith only [h101, h103, h9, hlam]
                      · linarith only [h101, h102, hc35, hlam, hphi, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h133 | h133
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h135 | h135
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h136 | h136
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h139 | h139
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                                    · linarith only [h1, h140, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                                      · linarith only [h1, h101, h133, h142, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h144 | h144
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h145 | h145
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                                            · linarith only [h1, h137, h144, h146, h9, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                                              · linarith only [h0, h1, h101, h144, h148, h5, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h150 | h150
                                                · linarith only [h0, h138, h146, h150, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                                · linarith only [h1, h144, h150, h9, hc23, hc34, hlam, hphi]
                                          · linarith only [h136, h142, h145, hc13, hlam, hphi, ht34, ht45, ht56, u6elo0]
                                        · linarith only [h137, h144, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h139, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h137, h138, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                                · linarith only [h0, h137, h157, h5, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h159 | h159
                                  · linarith only [h0, h137, h159, h5, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                  · linarith only [h159, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h101, h136, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                          · linarith only [h101, h133, h134, h135, hc36, hlam, hphi, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h164 | h164
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h165 | h165
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h168 | h168
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
                                    · linarith only [h1, h133, h169, h9, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                                      · linarith only [h1, h101, h133, h171, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h173 | h173
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h174 | h174
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                                            · linarith only [h1, h166, h173, h175, h9, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                                              · linarith only [h0, h1, h101, h167, h173, h175, h177, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h179 | h179
                                                · linarith only [h0, h167, h175, h179, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                                · linarith only [h1, h173, h179, h9, hc23, hc34, hlam, hphi]
                                          · linarith only [h165, h171, h174, hc13, hlam, hphi, ht34, ht45, ht56, u6elo0]
                                        · linarith only [h166, h173, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h168, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h166, h167, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h186 | h186
                                · linarith only [h0, h166, h186, h5, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h188 | h188
                                  · linarith only [h0, h166, h188, h5, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                  · linarith only [h188, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h134, h165, h9, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                          · linarith only [h133, h164, h9, hc36, hlam, hphi, u6elo4]
                      · linarith only [h133, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h8, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h195 | h195
                · rcases m.htr 0 3 4 (by decide) (by decide) with h196 | h196
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h197 | h197
                    · linarith only [h197, h5, h7, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h199 | h199
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h200 | h200
                        · linarith only [h200, h6, h7, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h202 | h202
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h203 | h203
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h206 | h206
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h207 | h207
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h208 | h208
                                      · linarith only [h1, h197, h208, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h210 | h210
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h211 | h211
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                                            · linarith only [h0, h204, h212, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                            · linarith only [h1, h197, h207, h212, hc23, hc35, hlam, hphi]
                                          · linarith only [h211, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h210, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h196, h197, h204, h207, hc23, hc35, hlam, hphi]
                                  · linarith only [h206, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h204, h205, h6, h7, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                              · linarith only [h204, h5, h7, hc12, hc25, hlam, hphi]
                            · linarith only [h203, h7, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h202, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h199, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h224 | h224
                    · linarith only [h224, h5, h7, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h226 | h226
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h227 | h227
                        · linarith only [h227, h6, h7, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h229 | h229
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h230 | h230
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h231 | h231
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h232 | h232
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h233 | h233
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                                    · linarith only [h1, h196, h234, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
                                      · linarith only [h1, h224, h236, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h238 | h238
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h239 | h239
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                                            · linarith only [h0, h1, h196, h231, h238, h240, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h242 | h242
                                              · linarith only [h0, h224, h232, h240, h242, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h244 | h244
                                                · linarith only [h0, h232, h240, h244, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                                · linarith only [h1, h196, h238, h244, hc23, hc34, hlam, hphi]
                                          · linarith only [h230, h239, hc15, hlam, hphi, ht56, u6elo0]
                                        · linarith only [h238, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h233, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h231, h232, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                              · linarith only [h231, h5, h7, hc12, hc25, hlam, hphi]
                            · linarith only [h230, h7, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h196, h226, h229, hc36, hlam, hphi, u6elo4]
                      · linarith only [h226, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h195, h5, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h256 | h256
              · rcases m.htr 0 2 6 (by decide) (by decide) with h257 | h257
                · rcases m.htr 0 3 4 (by decide) (by decide) with h258 | h258
                  · linarith only [h258, h5, h6, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h260 | h260
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h261 | h261
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h262 | h262
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h263 | h263
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h264 | h264
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                                · linarith only [h0, h266, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h268 | h268
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h269 | h269
                                    · linarith only [h1, h258, h260, h269, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h272 | h272
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h273 | h273
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                                            · linarith only [h0, h1, h258, h265, h271, h274, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h276 | h276
                                              · linarith only [h2, h265, h266, h276, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                              · linarith only [h1, h271, h276, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                          · linarith only [h273, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h272, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h258, h260, h265, h271, hc23, hc34, hlam, hphi]
                                  · linarith only [h268, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h265, h5, h6, hc12, hc24, hlam, hphi]
                            · linarith only [h264, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h263, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h256, h262, h6, hlam]
                      · linarith only [h261, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h288 | h288
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h290 | h290
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h291 | h291
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                                · linarith only [h0, h293, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h295 | h295
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                                    · linarith only [h1, h258, h296, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h298 | h298
                                      · linarith only [h1, h260, h298, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h300 | h300
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h301 | h301
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h302 | h302
                                            · linarith only [h1, h258, h302, h5, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                                              · linarith only [h0, h1, h260, h292, h300, h304, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h306 | h306
                                                · linarith only [h0, h292, h306, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                                · linarith only [h1, h260, h300, h306, hc23, hc35, hlam, hphi]
                                          · linarith only [h298, h301, hc13, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                        · linarith only [h260, h288, h292, h300, hc23, hc35, hlam, hphi]
                                  · linarith only [h295, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h292, h5, h6, hc12, hc24, hlam, hphi]
                            · linarith only [h260, h291, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                          · linarith only [h290, h6, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                        · linarith only [h256, h289, h6, hlam]
                      · linarith only [h288, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h257, h5, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h318 | h318
                · rcases m.htr 0 3 4 (by decide) (by decide) with h319 | h319
                  · linarith only [h319, h5, h6, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h321 | h321
                    · linarith only [h256, h321, h5, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h323 | h323
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h324 | h324
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h325 | h325
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h326 | h326
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                                · linarith only [h0, h328, h6, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h330 | h330
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h331 | h331
                                    · linarith only [h1, h319, h331, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h333 | h333
                                      · linarith only [h1, h321, h333, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h335 | h335
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h336 | h336
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                                            · linarith only [h0, h1, h319, h327, h335, h337, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h339 | h339
                                              · linarith only [h2, h321, h327, h328, h339, hc05, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h341 | h341
                                                · linarith only [h0, h327, h341, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                                · linarith only [h341, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h326, h336, hc15, hlam, hphi, ht56, u6elo0]
                                        · linarith only [h335, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h327, h330, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h256, h327, h5, hc12, hc25, hlam, hphi]
                            · linarith only [h256, h326, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h325, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h350 | h350
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h351 | h351
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h353 | h353
                                · linarith only [h0, h353, h6, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h355 | h355
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h356 | h356
                                    · linarith only [h1, h319, h356, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h358 | h358
                                      · linarith only [h1, h321, h358, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h360 | h360
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h361 | h361
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h362 | h362
                                            · linarith only [h0, h319, h352, h362, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h364 | h364
                                              · linarith only [h0, h1, h321, h352, h360, h364, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h366 | h366
                                                · linarith only [h2, h352, h353, h366, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                                · linarith only [h366, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h361, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h360, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h355, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h324, h352, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h324, h351, h6, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h350, h5, h6, hc23, hlam, hphi, ht34, ht45, ht56, u6elo4]
                      · linarith only [h323, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h318, h5, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h377 | h377
            · rcases m.htr 0 2 5 (by decide) (by decide) with h378 | h378
              · rcases m.htr 0 2 6 (by decide) (by decide) with h379 | h379
                · rcases m.htr 0 3 4 (by decide) (by decide) with h380 | h380
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h381 | h381
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h382 | h382
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h383 | h383
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h384 | h384
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h385 | h385
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                              · linarith only [h0, h386, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h389 | h389
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h392 | h392
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h393 | h393
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h395 | h395
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h396 | h396
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h397 | h397
                                                  · linarith only [h0, h388, h397, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h399 | h399
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h400 | h400
                                                      · linarith only [h1, h386, h388, h394, h397, h400, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h402 | h402
                                                        · linarith only [h1, h390, h402, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                        · linarith only [h402, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h399, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h396, h5, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h1, h391, h395, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                            · linarith only [h380, h394, h5, hlam]
                                          · linarith only [h393, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h392, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h1, h381, h386, h388, h391, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                    · linarith only [h1, h380, h386, h388, h390, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                  · linarith only [h388, h389, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h377, h388, h5, hc12, hc23, hlam, hphi]
                            · linarith only [h385, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h384, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h417 | h417
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h418 | h418
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                              · linarith only [h0, h419, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h422 | h422
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h424 | h424
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h425 | h425
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h426 | h426
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h427 | h427
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h428 | h428
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h429 | h429
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h430 | h430
                                                  · linarith only [h0, h383, h417, h421, h430, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h432 | h432
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                                                      · linarith only [h1, h380, h383, h417, h433, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h435 | h435
                                                        · linarith only [h1, h419, h421, h427, h435, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                        · linarith only [h383, h417, h435, hc34, hc45, hlam, hphi]
                                                    · linarith only [h432, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h429, h5, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h381, h428, h5, hlam]
                                            · linarith only [h380, h427, h5, hlam]
                                          · linarith only [h426, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h425, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h381, h419, h421, h424, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                    · linarith only [h1, h380, h419, h421, h423, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                  · linarith only [h421, h422, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h377, h421, h5, hc12, hc23, hlam, hphi]
                            · linarith only [h418, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h417, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h382, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · linarith only [h378, h381, h5, hlam]
                  · linarith only [h377, h380, h5, hlam]
                · linarith only [h379, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h454 | h454
                · rcases m.htr 0 3 4 (by decide) (by decide) with h455 | h455
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h456 | h456
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h457 | h457
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
                        · linarith only [h377, h378, h458, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h460 | h460
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h461 | h461
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                              · linarith only [h0, h377, h462, h5, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h464 | h464
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h465 | h465
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h466 | h466
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h467 | h467
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h468 | h468
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h469 | h469
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h470 | h470
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h471 | h471
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h472 | h472
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h473 | h473
                                                  · linarith only [h0, h458, h464, h473, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h475 | h475
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h476 | h476
                                                      · linarith only [h1, h378, h462, h464, h470, h473, h476, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h478 | h478
                                                        · linarith only [h1, h462, h464, h470, h478, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                        · linarith only [h478, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h378, h464, h469, h475, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                                · linarith only [h472, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h1, h467, h471, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                            · linarith only [h0, h455, h464, h470, h5, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                          · linarith only [h469, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h462, h464, h468, hc24, hlam, hphi, ht45, ht56, u6elo3]
                                      · linarith only [h1, h456, h462, h464, h467, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                    · linarith only [h1, h455, h462, h464, h466, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                  · linarith only [h464, h465, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h377, h378, h464, hc12, hc25, hlam, hphi]
                            · linarith only [h378, h461, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h460, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h457, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h494 | h494
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h495 | h495
                        · linarith only [h377, h456, h495, h5, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h497 | h497
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h498 | h498
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
                              · linarith only [h0, h377, h499, h5, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h501 | h501
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h502 | h502
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h503 | h503
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h504 | h504
                                      · linarith only [h0, h1, h456, h5, h501, h504, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h506 | h506
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h507 | h507
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h508 | h508
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h509 | h509
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h510 | h510
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h511 | h511
                                                  · linarith only [h0, h456, h495, h5, h501, h509, h511, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h513 | h513
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h514 | h514
                                                      · linarith only [h0, h456, h5, h501, h508, h509, h511, h514, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h516 | h516
                                                        · linarith only [h0, h456, h5, h501, h508, h509, h516, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                        · linarith only [h516, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h456, h5, h501, h509, h513, hc24, hc56, hlam, hphi, ht45]
                                                · linarith only [h456, h5, h509, h510, hc02, hc36, hlam, hphi, ht23]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h521 | h521
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h522 | h522
                                                  · linarith only [h0, h5, h501, h509, h522, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h524 | h524
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h525 | h525
                                                      · linarith only [h378, h455, h5, h509, h522, h525, hc02, hc35, hlam, hphi, ht23]
                                                      · linarith only [h0, h5, h501, h508, h509, h525, hc34, hc45, hlam, hphi]
                                                    · linarith only [h0, h5, h501, h508, h509, h524, hc34, hc56, hlam, hphi, ht45]
                                                · linarith only [h0, h5, h501, h508, h521, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                            · linarith only [h455, h5, h508, hlam]
                                          · linarith only [h504, h507, hc13, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                        · linarith only [h499, h501, h506, hc24, hlam, hphi, ht45, ht56, u6elo3]
                                    · linarith only [h455, h499, h501, h503, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h501, h502, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h377, h5, h501, hc12, hc23, hlam, hphi]
                            · linarith only [h498, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h497, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h494, h5, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                  · linarith only [h377, h455, h5, hlam]
                · linarith only [h377, h454, hc24, hlam, hphi, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h541 | h541
              · rcases m.htr 0 2 6 (by decide) (by decide) with h542 | h542
                · rcases m.htr 0 3 4 (by decide) (by decide) with h543 | h543
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h544 | h544
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h545 | h545
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h546 | h546
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h547 | h547
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h548 | h548
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h549 | h549
                              · linarith only [h0, h5, h549, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h551 | h551
                                · linarith only [h0, h377, h541, h551, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h553 | h553
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h555 | h555
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h556 | h556
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h557 | h557
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h558 | h558
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h559 | h559
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h560 | h560
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h561 | h561
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h562 | h562
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h563 | h563
                                                      · linarith only [h1, h554, h563, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h565 | h565
                                                        · linarith only [h541, h561, h563, h565, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                        · linarith only [h565, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h561, h562, hc45, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h377, h546, h561, hlam]
                                                · linarith only [h560, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h5, h544, h559, hlam]
                                            · linarith only [h5, h543, h558, hlam]
                                          · linarith only [h557, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h556, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h544, h551, h553, h554, h555, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                    · linarith only [h1, h543, h549, h553, h554, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                  · linarith only [h553, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h548, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h547, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h377, h541, h546, hlam]
                      · linarith only [h545, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · linarith only [h377, h541, h543, h544, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h583 | h583
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h584 | h584
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h585 | h585
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h586 | h586
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h587 | h587
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                              · linarith only [h0, h5, h588, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h590 | h590
                                · linarith only [h0, h377, h590, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h592 | h592
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h593 | h593
                                    · linarith only [h1, h5, h541, h543, h587, h593, hc56, hlam, hphi, ht0b, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h595 | h595
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h596 | h596
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h597 | h597
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h598 | h598
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h599 | h599
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h600 | h600
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h601 | h601
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h602 | h602
                                                    · linarith only [h5, h541, h543, h598, h602, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                    · linarith only [h602, hc25, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h5, h543, h585, h598, h601, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                                · linarith only [h543, h598, h600, hc04, hlam, hphi, ht45, ht56, u6elo3]
                                              · linarith only [h3, h5, h541, h543, h597, h598, h599, hc35, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h608 | h608
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h609 | h609
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h610 | h610
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h611 | h611
                                                    · linarith only [h5, h541, h598, h611, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                    · linarith only [h610, h611, hc45, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h377, h585, h610, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                                · linarith only [h5, h609, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h5, h583, h608, hlam]
                                          · linarith only [h597, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h596, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h583, h588, h592, h595, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h592, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h587, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h586, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h5, h541, h543, h585, hlam]
                      · linarith only [h5, h584, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                    · linarith only [h5, h541, h583, hlam]
                · linarith only [h541, h542, hc25, hlam, hphi, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h627 | h627
                · rcases m.htr 0 3 4 (by decide) (by decide) with h628 | h628
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h629 | h629
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h630 | h630
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h631 | h631
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h632 | h632
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h633 | h633
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
                              · linarith only [h0, h5, h634, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
                                · linarith only [h0, h377, h636, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h638 | h638
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h639 | h639
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h640 | h640
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h641 | h641
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h642 | h642
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h644 | h644
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h645 | h645
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h646 | h646
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h647 | h647
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h648 | h648
                                                      · linarith only [h1, h639, h648, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h650 | h650
                                                        · linarith only [h1, h628, h631, h648, h650, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                        · linarith only [h650, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h541, h638, h642, h647, hc15, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                                  · linarith only [h377, h631, h646, hlam]
                                                · linarith only [h377, h643, h645, hc04, hlam, hphi, ht45, ht56, u6elo3]
                                              · linarith only [h1, h5, h640, h644, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                            · linarith only [h5, h628, h643, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                          · linarith only [h642, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h636, h638, h639, h641, hc26, hlam, hphi, u6elo3]
                                      · linarith only [h1, h629, h636, h638, h639, h640, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                    · linarith only [h1, h628, h634, h638, h639, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                  · linarith only [h638, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h541, h627, h633, hc26, hlam, hphi, u6elo5]
                          · linarith only [h632, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h665 | h665
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h666 | h666
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
                              · linarith only [h0, h5, h628, h667, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h669 | h669
                                · linarith only [h0, h377, h669, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h671 | h671
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h672 | h672
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h673 | h673
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h674 | h674
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h675 | h675
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h676 | h676
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h677 | h677
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h678 | h678
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h679 | h679
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h680 | h680
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h681 | h681
                                                      · linarith only [h377, h628, h631, h681, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h683 | h683
                                                        · linarith only [h1, h672, h683, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                        · linarith only [h683, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h377, h631, h671, h675, h678, h679, h680, hc15, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h687 | h687
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h688 | h688
                                                      · linarith only [h0, h377, h671, h678, h679, h688, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h690 | h690
                                                        · linarith only [h1, h673, h688, h690, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                        · linarith only [h690, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h377, h671, h678, h679, h687, hc36, hlam, hphi, u6elo5]
                                                · linarith only [h5, h678, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h377, h629, h676, h677, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                            · linarith only [h5, h628, h676, hlam]
                                          · linarith only [h675, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h672, h674, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                      · linarith only [h629, h672, h673, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                    · linarith only [h628, h667, h671, h672, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h671, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h377, h627, h631, h666, hc26, hlam, hphi, u6elo5]
                          · linarith only [h377, h627, h665, hc26, hlam, hphi, u6elo4]
                      · linarith only [h630, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h705 | h705
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h706 | h706
                        · linarith only [h628, h629, h706, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h708 | h708
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h709 | h709
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h710 | h710
                              · linarith only [h0, h5, h627, h710, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h712 | h712
                                · linarith only [h0, h377, h712, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h714 | h714
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h715 | h715
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h716 | h716
                                      · linarith only [h1, h2, h628, h629, h712, h714, h716, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h718 | h718
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h719 | h719
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h720 | h720
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h721 | h721
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h722 | h722
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h723 | h723
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h724 | h724
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h725 | h725
                                                      · linarith only [h2, h628, h629, h706, h712, h714, h721, h722, h725, hc23, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h727 | h727
                                                        · linarith only [h1, h629, h715, h720, h723, h725, h727, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                        · linarith only [h727, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h724, hc25, hlam, hphi, ht56, u6elo5]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h731 | h731
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h732 | h732
                                                      · linarith only [h0, h377, h714, h722, h723, h732, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h734 | h734
                                                        · linarith only [h1, h715, h734, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                        · linarith only [h0, h377, h714, h722, h723, h734, hc34, hc36, hc45, hlam, hphi, u6elo4]
                                                    · linarith only [h629, h721, h731, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                                · linarith only [h377, h628, h629, h721, h722, hc02, hc36, hlam, hphi, ht23]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h739 | h739
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h740 | h740
                                                  · linarith only [h2, h706, h712, h714, h720, h721, h739, h740, hc35, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h742 | h742
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h743 | h743
                                                      · linarith only [h1, h715, h740, h743, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h745 | h745
                                                        · linarith only [h3, h715, h716, h745, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                        · linarith only [h745, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h377, h714, h720, h721, h739, h742, hc36, hlam, hphi, u6elo5]
                                                · linarith only [h377, h720, h739, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h0, h5, h628, h714, h720, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                          · linarith only [h709, h716, h719, hc13, hlam, hphi, ht34, ht45, ht56, u6elo0]
                                        · linarith only [h718, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h628, h629, h710, h714, h715, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h714, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h709, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h377, h708, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                      · linarith only [h705, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h758 | h758
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h759 | h759
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h760 | h760
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h761 | h761
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h762 | h762
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h763 | h763
                              · linarith only [h0, h5, h627, h763, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h765 | h765
                                · linarith only [h0, h377, h765, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h767 | h767
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h768 | h768
                                    · linarith only [h1, h541, h628, h758, h768, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h770 | h770
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h771 | h771
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h772 | h772
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h773 | h773
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h774 | h774
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h775 | h775
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h776 | h776
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h777 | h777
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h778 | h778
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h779 | h779
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h780 | h780
                                                          · linarith only [h628, h758, h773, h780, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                          · linarith only [h780, hc35, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h628, h779, hc03, hlam, hphi, ht34, ht45, ht56, u6elo4]
                                                      · linarith only [h0, h541, h628, h758, h760, h767, h775, h778, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                                    · linarith only [h0, h541, h767, h775, h777, hc36, hlam, hphi, u6elo5]
                                                  · linarith only [h0, h377, h758, h760, h767, h775, h776, hc36, hlam, hphi, ht0b, ht6b, u0elo2]
                                                · linarith only [h628, h773, h775, hc03, hc36, hlam, hphi]
                                              · linarith only [h0, h541, h628, h758, h767, h770, h773, h774, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h789 | h789
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h790 | h790
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h791 | h791
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h792 | h792
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h793 | h793
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h794 | h794
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h795 | h795
                                                          · linarith only [h1, h770, h795, hc56, hlam, hphi, ht0b, ht6b, u0elo0]
                                                          · linarith only [h795, hc35, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h773, h794, hc23, hlam, hphi, ht34, ht45, ht56, u6elo4]
                                                      · linarith only [h541, h773, h789, h793, hc02, hc45, hlam, hphi, ht23, ht34]
                                                    · linarith only [h0, h541, h767, h790, h792, hc36, hlam, hphi, u6elo5]
                                                  · linarith only [h0, h541, h760, h767, h773, h789, h790, h791, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                                · linarith only [h541, h789, h790, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h0, h1, h5, h758, h767, h789, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                          · linarith only [h772, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h771, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h758, h763, h767, h770, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h767, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h762, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h761, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h628, h758, h760, hlam]
                      · linarith only [h759, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h812 | h812
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h813 | h813
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h814 | h814
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h815 | h815
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h816 | h816
                              · linarith only [h0, h5, h627, h816, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h818 | h818
                                · linarith only [h0, h377, h813, h818, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h820 | h820
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h821 | h821
                                    · linarith only [h1, h628, h821, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h823 | h823
                                      · linarith only [h1, h758, h823, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h825 | h825
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h826 | h826
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h827 | h827
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h828 | h828
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h829 | h829
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h830 | h830
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h831 | h831
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h832 | h832
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h833 | h833
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h834 | h834
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h835 | h835
                                                            · rcases h0bigk with h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h0, h820, h829, h833, h835, hc56, hlam, hphi, ht0b, ht6b, p836_1, u0elo0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h0, h5, h820, h829, h833, h835, hc56, hlam, hphi, ht0b, ht6b, p836_1, u0elo0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h813, h835, hc56, hlam, hphi, ht0b, ht6b, p836_1, u0elo0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h0, h5, h758, h820, h829, h833, h835, hc56, hlam, hphi, ht0b, ht6b, p836_1, u0elo0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                rcases p836_3 (m.d 0 1) (by simp) with h842 | h842
                                                                · rcases p836_3 (m.d 0 2) (by simp) with h843 | h843
                                                                  · linarith only [h0, h843, hlam]
                                                                  · linarith only [h627, h843, hlam]
                                                                · linarith only [h4, h842, hlam]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h0, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h5, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h377, hlam, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h541, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h5, h758, h827, h832, hc06, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h1, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h758, h827, h832, hc02, hc23, hlam, hphi, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h628, hlam, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h758, hlam, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h627, h758, h827, h829, h832, h833, h835, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h2, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h0, h820, h829, h833, h835, hc56, hlam, hphi, ht0b, ht6b, p836_1, u0elo3]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h0, h5, h628, h820, h827, h829, h833, h835, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h0, h5, h628, h758, h820, h827, h829, h833, h835, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                rcases p836_3 (m.d 0 1) (by simp) with h864 | h864
                                                                · rcases p836_3 (m.d 0 2) (by simp) with h865 | h865
                                                                  · linarith only [h377, h865, hlam]
                                                                  · linarith only [h627, h865, hlam]
                                                                · linarith only [h4, h864, hlam]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h3, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h0, h820, h829, h833, h835, hc56, hlam, hphi, ht0b, ht6b, p836_1, u0elo4]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h0, h5, h758, h820, h827, h829, h832, h833, h835, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h813, hlam, p836_1]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                rcases p836_3 (m.d 0 1) (by simp) with h874 | h874
                                                                · rcases p836_3 (m.d 0 2) (by simp) with h875 | h875
                                                                  · linarith only [h541, h875, hlam]
                                                                  · linarith only [h627, h875, hlam]
                                                                · linarith only [h4, h874, hlam]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h4, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h627, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h812, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h814, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [h815, hlam, p836_0]
                                                              · obtain ⟨p836_0, p836_1, p836_2, p836_3⟩ := h836c
                                                                linarith only [hlam, p836_0]
                                                            · linarith only [h835, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h0, h5, h758, h820, h831, h834, hlam]
                                                        · linarith only [h5, h758, h832, h833, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                                                      · linarith only [h628, h813, h832, hlam]
                                                    · linarith only [h758, h828, h831, hc05, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h0, h3, h377, h813, h820, h829, h830, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                                · linarith only [h829, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h5, h628, h827, h828, hc02, hc35, hlam, hphi, ht23]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h893 | h893
                                              · linarith only [h0, h5, h758, h820, h827, h893, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h895 | h895
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h896 | h896
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h897 | h897
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h898 | h898
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h899 | h899
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h900 | h900
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h901 | h901
                                                            · rcases h0bigk with h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, h820, h895, h899, h901, hc56, hlam, hphi, ht0b, ht6b, p902_1, u0elo0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, h5, h820, h895, h899, h901, hc56, hlam, hphi, ht0b, ht6b, p902_1, u0elo0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h813, hc45, hlam, hphi, ht0b, ht56, ht6b, p902_1, u0elo0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, h541, h820, h895, h899, h901, hc56, hlam, hphi, ht0b, ht6b, p902_1, u0elo0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                rcases p902_3 (m.d 0 1) (by simp) with h908 | h908
                                                                · rcases p902_3 (m.d 0 2) (by simp) with h909 | h909
                                                                  · linarith only [h0, h909, hlam]
                                                                  · linarith only [h627, h909, hlam]
                                                                · linarith only [h4, h908, hlam]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h5, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h377, hlam, p902_1]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h541, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h4, h5, h893, h898, hc16, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p902_1]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h1, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, h758, h820, h895, h899, h901, hc56, hlam, hphi, ht0b, ht6b, p902_1, u0elo4]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h628, hlam, p902_1]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h758, hlam, p902_1]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                rcases p902_3 (m.d 0 1) (by simp) with h924 | h924
                                                                · rcases p902_3 (m.d 0 2) (by simp) with h925 | h925
                                                                  · linarith only [h5, h925, hlam]
                                                                  · linarith only [h627, h925, hlam]
                                                                · linarith only [h4, h924, hlam]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h2, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, h820, h895, h899, h901, hc56, hlam, hphi, ht0b, ht6b, p902_1, u0elo3]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, h2, h5, h820, h895, h899, h901, hc56, hlam, hphi, ht0b, ht6b, p902_1, u0elo0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, h2, h5, h758, h820, h895, h899, h901, hc56, hlam, hphi, ht0b, ht6b, p902_1, u0elo0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                rcases p902_3 (m.d 0 1) (by simp) with h934 | h934
                                                                · rcases p902_3 (m.d 0 2) (by simp) with h935 | h935
                                                                  · linarith only [h377, h935, hlam]
                                                                  · linarith only [h627, h935, hlam]
                                                                · linarith only [h4, h934, hlam]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h3, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, h820, h895, h899, h901, hc56, hlam, hphi, ht0b, ht6b, p902_1, u0elo4]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h0, h3, h5, h820, h895, h899, h901, hc56, hlam, hphi, ht0b, ht6b, p902_1, u0elo0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h813, hlam, p902_1]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                rcases p902_3 (m.d 0 1) (by simp) with h944 | h944
                                                                · rcases p902_3 (m.d 0 2) (by simp) with h945 | h945
                                                                  · linarith only [h541, h945, hlam]
                                                                  · linarith only [h627, h945, hlam]
                                                                · linarith only [h4, h944, hlam]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h4, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h627, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h812, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h814, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [h815, hlam, p902_0]
                                                              · obtain ⟨p902_0, p902_1, p902_2, p902_3⟩ := h902c
                                                                linarith only [hlam, p902_0]
                                                            · linarith only [h901, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h0, h5, h820, h893, h897, h900, hlam]
                                                        · linarith only [h5, h893, h898, h899, hc02, hc46, hlam, hphi, ht23, ht34]
                                                      · linarith only [h628, h813, h898, hlam]
                                                    · linarith only [h541, h897, hc05, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h377, h813, h896, hlam]
                                                · linarith only [h0, h5, h820, h895, hc26, hlam, hphi, u6elo3]
                                          · linarith only [h826, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h825, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h820, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h815, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h814, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h967 | h967
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h968 | h968
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h969 | h969
                              · linarith only [h0, h5, h969, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h971 | h971
                                · linarith only [h0, h377, h5, h628, h971, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h973 | h973
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h974 | h974
                                    · linarith only [h1, h628, h974, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h976 | h976
                                      · linarith only [h1, h758, h976, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h978 | h978
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h979 | h979
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h980 | h980
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h981 | h981
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h982 | h982
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h983 | h983
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h984 | h984
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h985 | h985
                                                      · linarith only [h5, h628, h813, h980, h985, hc02, hc23, hlam, hphi]
                                                      · linarith only [h0, h5, h628, h973, h982, h983, h985, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                    · linarith only [h984, hc25, hlam, hphi, ht56, u6elo5]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h989 | h989
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h990 | h990
                                                      · linarith only [h0, h377, h973, h982, h983, h990, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h992 | h992
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h993 | h993
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h994 | h994
                                                            · rcases h0bigk with h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, h973, h982, h992, h994, hc56, hlam, hphi, ht0b, ht6b, p995_1, u0elo0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, h5, h973, h982, h992, h994, hc56, hlam, hphi, ht0b, ht6b, p995_1, u0elo0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, h5, h628, h973, h982, h992, h994, hc56, hlam, hphi, ht0b, ht6b, p995_1, u0elo0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, h5, h628, h813, h973, h982, h992, h994, hc56, hlam, hphi, ht0b, ht6b, p995_1, u0elo0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                rcases p995_3 (m.d 0 1) (by simp) with h1001 | h1001
                                                                · rcases p995_3 (m.d 0 2) (by simp) with h1002 | h1002
                                                                  · linarith only [h0, h1002, hlam]
                                                                  · linarith only [h1002, h627, hlam]
                                                                · linarith only [h1001, h4, hlam]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h5, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h377, hlam, p995_1]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h541, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h4, h5, h628, h980, h983, hc16, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p995_1]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h1, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, h628, h980, hc12, hc24, hlam, hphi, p995_1]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h628, hlam, p995_1]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h758, hlam, p995_1]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h627, h628, h980, h982, h983, h992, h994, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p995_1]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h2, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, h973, h982, h992, h994, hc56, hlam, hphi, ht0b, ht6b, p995_1, u0elo3]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h628, h980, h983, hc03, hc45, hlam, hphi, ht34, p995_1]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h813, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                rcases p995_3 (m.d 0 1) (by simp) with h1023 | h1023
                                                                · rcases p995_3 (m.d 0 2) (by simp) with h1024 | h1024
                                                                  · linarith only [h1024, h377, hlam]
                                                                  · linarith only [h1024, h627, hlam]
                                                                · linarith only [h1023, h4, hlam]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h3, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, h973, h982, h992, h994, hc56, hlam, hphi, ht0b, ht6b, p995_1, u0elo4]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, h3, h5, h973, h982, h992, h994, hc56, hlam, hphi, ht0b, ht6b, p995_1, u0elo0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h0, h3, h377, h973, h982, h992, h994, hc56, hlam, hphi, ht0b, ht6b, p995_1, u0elo0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                rcases p995_3 (m.d 0 1) (by simp) with h1033 | h1033
                                                                · rcases p995_3 (m.d 0 2) (by simp) with h1034 | h1034
                                                                  · linarith only [h1034, h541, hlam]
                                                                  · linarith only [h1034, h627, hlam]
                                                                · linarith only [h1033, h4, hlam]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h4, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h627, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h812, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h967, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [h968, hlam, p995_0]
                                                              · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                                                linarith only [hlam, p995_0]
                                                            · linarith only [h980, h983, h994, hc34, hlam, hphi, ht45, ht56, u6elo5]
                                                          · linarith only [h0, h5, h628, h758, h973, h980, h983, h989, h993, hc05, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b]
                                                        · linarith only [h5, h628, h992, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                                                    · linarith only [h989, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h982, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h5, h628, h980, h981, hc02, hc35, hlam, hphi, ht23]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1050 | h1050
                                              · linarith only [h0, h1050, h5, h758, h973, h980, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1052 | h1052
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1053 | h1053
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1054 | h1054
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1055 | h1055
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1056 | h1056
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h1057 | h1057
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h1058 | h1058
                                                            · rcases h0bigk with h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, h1052, h1056, h1058, h973, hc56, hlam, hphi, ht0b, ht6b, p1059_1, u0elo0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, h1052, h1056, h1058, h5, h973, hc56, hlam, hphi, ht0b, ht6b, p1059_1, u0elo0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, h1052, h1056, h1058, h377, h973, hc56, hlam, hphi, ht0b, ht6b, p1059_1, u0elo0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, h1052, h1056, h1058, h541, h973, hc56, hlam, hphi, ht0b, ht6b, p1059_1, u0elo0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                rcases p1059_3 (m.d 0 1) (by simp) with h1065 | h1065
                                                                · rcases p1059_3 (m.d 0 2) (by simp) with h1066 | h1066
                                                                  · linarith only [h0, h1066, hlam]
                                                                  · linarith only [h1066, h627, hlam]
                                                                · linarith only [h1065, h4, hlam]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h5, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h377, hlam, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h541, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h1050, h4, h5, hc16, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h1, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, h628, h813, h973, hc26, hlam, hphi, ht0b, ht6b, p1059_1, u0elo4]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h628, hlam, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h758, hlam, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h1052, h1053, h1056, h1058, h627, h628, h813, h980, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h2, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, h1052, h1053, h1056, h1058, h813, h973, h980, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h1053, h813, h980, hc03, hc34, hlam, hphi, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h813, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h1052, h1053, h1056, h1058, h627, h813, h980, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h3, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, h1052, h1053, h1056, h1058, h813, h973, h980, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, h1052, h1053, h1056, h1058, h5, h813, h973, h980, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h0, h1052, h1053, h1056, h1058, h377, h813, h973, h980, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1059_1]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                rcases p1059_3 (m.d 0 1) (by simp) with h1093 | h1093
                                                                · rcases p1059_3 (m.d 0 2) (by simp) with h1094 | h1094
                                                                  · linarith only [h1094, h541, hlam]
                                                                  · linarith only [h1094, h627, hlam]
                                                                · linarith only [h1093, h4, hlam]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h4, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h627, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h812, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h967, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [h968, hlam, p1059_0]
                                                              · obtain ⟨p1059_0, p1059_1, p1059_2, p1059_3⟩ := h1059c
                                                                linarith only [hlam, p1059_0]
                                                            · linarith only [h1058, h813, hc05, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h0, h1050, h1054, h1057, h5, h973, hlam]
                                                        · linarith only [h1053, h1056, h5, h628, h813, h980, hc02, hc46, hlam, hphi, ht23, ht34]
                                                      · linarith only [h1053, h1055, h980, hlam]
                                                    · linarith only [h1054, hc25, hlam, hphi, ht56, u6elo5]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1109 | h1109
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1110 | h1110
                                                      · linarith only [h0, h1052, h1053, h1110, h377, h973, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                      · linarith only [h0, h1052, h1110, h5, h973, h980, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h0, h1052, h1053, h1109, h5, h973, h980, hc36, hlam, hphi, u6elo5]
                                                · linarith only [h0, h1052, h5, h973, hc26, hlam, hphi, u6elo3]
                                          · linarith only [h969, h973, h976, h979, hc26, hlam, hphi, u6elo5]
                                        · linarith only [h969, h973, h978, hc26, hlam, hphi, u6elo3]
                                  · linarith only [h973, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h5, h627, h628, h813, h968, hc26, hlam, hphi, u6elo5]
                          · linarith only [h5, h627, h628, h967, hc26, hlam, hphi, u6elo4]
                      · linarith only [h5, h627, h812, hc26, hlam, hphi, u6elo3]
                · linarith only [h627, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
        · linarith only [h4, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h1123 | h1123
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1124 | h1124
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1125 | h1125
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1126 | h1126
              · linarith only [h0, h1126, h3, hlam]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1128 | h1128
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1129 | h1129
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1130 | h1130
                    · linarith only [h1, h1130, h3, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1132 | h1132
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1133 | h1133
                        · linarith only [h1133, h2, h3, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1135 | h1135
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1136 | h1136
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1137 | h1137
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1138 | h1138
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1139 | h1139
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1140 | h1140
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1141 | h1141
                                      · linarith only [h1, h1130, h1141, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                      · linarith only [h0, h1137, h1141, h3, hc23, hc35, hlam, hphi]
                                    · linarith only [h1129, h1130, h1140, hc13, hc35, hlam, hphi]
                                  · linarith only [h1137, h1139, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h1125, h1137, h1138, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                              · linarith only [h1124, h1126, h1137, hc12, hc25, hlam, hphi]
                            · linarith only [h1136, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1135, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h1132, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1151 | h1151
                    · linarith only [h1, h1151, h3, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1153 | h1153
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1154 | h1154
                        · linarith only [h0, h1125, h1154, h3, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1156 | h1156
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1157 | h1157
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1158 | h1158
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1159 | h1159
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1160 | h1160
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1161 | h1161
                                    · linarith only [h1, h1129, h1161, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1163 | h1163
                                      · linarith only [h1, h1151, h1163, h3, hlam]
                                      · linarith only [h0, h1158, h1163, h3, hc23, hc35, hlam, hphi]
                                  · linarith only [h1158, h1160, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h1125, h1158, h1159, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                              · linarith only [h1124, h1126, h1158, hc12, hc25, hlam, hphi]
                            · linarith only [h1157, h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h1156, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h1153, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h1128, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1173 | h1173
              · linarith only [h1125, h1173, h2, h3, hlam]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1175 | h1175
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1176 | h1176
                  · linarith only [h1124, h1125, h1176, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1178 | h1178
                    · linarith only [h1124, h1125, h1178, h2, h3, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1180 | h1180
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1181 | h1181
                        · linarith only [h1181, h2, h3, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1183 | h1183
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1184 | h1184
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1185 | h1185
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1186 | h1186
                                · linarith only [h0, h1125, h1186, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1188 | h1188
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1189 | h1189
                                    · linarith only [h1, h1176, h1189, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo4]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1191 | h1191
                                      · linarith only [h0, h1, h1176, h1178, h1185, h1191, h3, hc23, hc34, hlam, hphi]
                                      · linarith only [h0, h1185, h1191, h3, hc23, hc35, hlam, hphi]
                                  · linarith only [h1185, h1188, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1124, h1125, h1185, hc12, hc24, hlam, hphi]
                            · linarith only [h1184, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1125, h1183, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                      · linarith only [h1, h1180, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h1124, h1175, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1200 | h1200
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1201 | h1201
              · linarith only [h0, h1201, h3, hlam]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1203 | h1203
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1204 | h1204
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1205 | h1205
                    · linarith only [h1, h1205, h3, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1207 | h1207
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1208 | h1208
                        · linarith only [h1208, h2, h3, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1210 | h1210
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1211 | h1211
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1212 | h1212
                              · linarith only [h0, h1124, h1200, h1212, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1214 | h1214
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1215 | h1215
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1216 | h1216
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1217 | h1217
                                      · linarith only [h1, h1205, h1217, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo4]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1219 | h1219
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1220 | h1220
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1221 | h1221
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1222 | h1222
                                              · linarith only [h0, h1214, h1217, h1221, h1222, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1224 | h1224
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1225 | h1225
                                                  · linarith only [h1, h1208, h1212, h1214, h1225, hc05, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1227 | h1227
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1228 | h1228
                                                      · linarith only [h1, h1201, h1212, h1214, h1221, h1225, h1228, h3, hlam]
                                                      · linarith only [h1, h1212, h1214, h1217, h1221, h1228, h3, hc34, hc45, hlam, hphi]
                                                    · linarith only [h1, h1201, h1212, h1214, h1221, h1227, h3, hc34, hc56, hlam, hphi, ht45]
                                                · linarith only [h1, h1124, h1212, h1214, h1217, h1221, h1224, h3, hc02, hc34, hc35, hlam, hphi, ht23, ht45, ht56, u6elo3]
                                            · linarith only [h0, h1124, h1204, h1214, h1221, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                          · linarith only [h1, h1220, h3, hc13, hc56, hlam, hphi, ht34, ht45]
                                        · linarith only [h1212, h1214, h1219, hc24, hlam, hphi, ht45, ht56, u6elo3]
                                    · linarith only [h1, h1204, h1212, h1214, h1216, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                  · linarith only [h1214, h1215, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h1124, h1200, h1214, hc12, hc23, hlam, hphi]
                            · linarith only [h1211, h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h1210, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h1124, h1207, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                  · linarith only [h1124, h1200, h1204, hlam]
                · linarith only [h1203, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1244 | h1244
              · linarith only [h0, h1244, h3, hlam]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1246 | h1246
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1247 | h1247
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1248 | h1248
                    · linarith only [h1, h1248, h3, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1250 | h1250
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1251 | h1251
                        · linarith only [h1, h1247, h1251, h3, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1253 | h1253
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1254 | h1254
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1255 | h1255
                              · linarith only [h0, h1124, h1255, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1257 | h1257
                                · linarith only [h0, h1200, h1257, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo4]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1259 | h1259
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1260 | h1260
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1261 | h1261
                                      · linarith only [h1, h1248, h1261, h3, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1263 | h1263
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1264 | h1264
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1265 | h1265
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1266 | h1266
                                              · linarith only [h1, h1260, h1261, h1266, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1268 | h1268
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1269 | h1269
                                                  · linarith only [h1251, h1257, h1259, h1265, h1266, h1268, h1269, h2, hc35, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1271 | h1271
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1272 | h1272
                                                      · linarith only [h1, h1260, h1269, h1272, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                                      · linarith only [h1, h1260, h1261, h1272, h3, hc34, hc45, hlam, hphi]
                                                    · linarith only [h1244, h1271, hc05, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h1, h1260, h1261, h1268, h3, hc23, hc34, hc35, hlam, hphi, ht45, ht56, u6elo3]
                                            · linarith only [h1, h1124, h1260, h1261, h1265, h3, hc03, hc35, hlam, hphi]
                                          · linarith only [h1, h1260, h1264, h3, hc34, hc56, hlam, hphi, ht45]
                                        · linarith only [h1260, h1263, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                    · linarith only [h1247, h1248, h1260, hc13, hc35, hlam, hphi]
                                  · linarith only [h1259, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1254, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1253, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h1250, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1285 | h1285
                    · linarith only [h1, h1285, h3, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1287 | h1287
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1288 | h1288
                        · linarith only [h1288, h2, h3, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1290 | h1290
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1291 | h1291
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1292 | h1292
                              · linarith only [h0, h1124, h1246, h1292, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1294 | h1294
                                · linarith only [h1, h1200, h1247, h1292, h1294, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1296 | h1296
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1297 | h1297
                                    · linarith only [h1, h1247, h1297, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo4]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1299 | h1299
                                      · linarith only [h1, h1285, h1299, h3, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1301 | h1301
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1302 | h1302
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1303 | h1303
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1304 | h1304
                                              · linarith only [h0, h1296, h1299, h1304, h3, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                              · linarith only [h0, h1124, h1247, h1296, h1303, h1304, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1307 | h1307
                                              · linarith only [h0, h1124, h1285, h1296, h1303, h1307, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1309 | h1309
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1310 | h1310
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1311 | h1311
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1312 | h1312
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1313 | h1313
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h1314 | h1314
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h1315 | h1315
                                                            · rcases h0bigk with h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h0, h1296, h1309, h1313, h1315, hc56, hlam, hphi, ht0b, ht6b, p1316_1, u0elo0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h0, h1124, h1296, h1309, h1313, h1315, h3, hc15, hc56, hlam, hphi, ht01, ht0b, ht6b, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h0, h1124, h1247, h1296, h1309, h1313, h1315, h3, hc15, hc56, hlam, hphi, ht01, ht0b, ht6b, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h3, hlam, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                rcases p1316_3 (m.d 0 1) (by simp) with h1322 | h1322
                                                                · rcases p1316_3 (m.d 0 2) (by simp) with h1323 | h1323
                                                                  · linarith only [h0, h1323, hlam]
                                                                  · linarith only [h1246, h1323, hlam]
                                                                · linarith only [h1123, h1322, hlam]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h0, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1124, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1200, hlam, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1244, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1123, h1124, h1307, h1312, hc16, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h0, h1247, h1296, h1309, h1313, h1315, hc56, hlam, hphi, ht0b, ht6b, p1316_1, u0elo3]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1247, hlam, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1285, hlam, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1246, h1247, h1288, h1303, h1309, h1310, h1313, h1315, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h2, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h0, h1288, h1296, h1303, h1309, h1310, h1313, h1315, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1288, h1303, h1310, hc03, hc34, hlam, hphi, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1288, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1246, h1288, h1303, h1309, h1310, h1313, h1315, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1288, h1303, h1310, hc01, hc34, hlam, hphi, ht12, ht23, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h0, h1288, h1296, h1303, h1309, h1310, h1313, h1315, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1, h1288, h1292, h1296, h1303, h1309, h1310, h1313, h1315, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1288, h1292, h1296, h1297, h1303, h1309, h1310, h1313, h1315, h2, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1316_1]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                rcases p1316_3 (m.d 0 1) (by simp) with h1350 | h1350
                                                                · linarith only [h1350, h3, hlam]
                                                                · linarith only [h1123, h1350, hlam]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1123, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1246, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1287, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1290, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [h1291, hlam, p1316_0]
                                                              · obtain ⟨p1316_0, p1316_1, p1316_2, p1316_3⟩ := h1316c
                                                                linarith only [hlam, p1316_0]
                                                            · linarith only [h1288, h1315, hc05, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h1292, h1296, h1297, h1299, h1311, h1314, h2, h3, hlam]
                                                        · linarith only [h1288, h1292, h1297, h1303, h1310, h1313, h2, h3, hc12, hc46, hlam, hphi, ht23, ht34]
                                                      · linarith only [h1303, h1310, h1312, hlam]
                                                    · linarith only [h1288, h1292, h1296, h1297, h1309, h1310, h1311, h2, h3, hc36, hlam, hphi, u6elo5]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1364 | h1364
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1365 | h1365
                                                      · linarith only [h0, h1200, h1296, h1309, h1310, h1365, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                      · linarith only [h0, h1124, h1296, h1303, h1309, h1365, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h1244, h1292, h1296, h1297, h1309, h1364, h2, h3, hc36, hlam, hphi, u6elo5]
                                                · linarith only [h1124, h1309, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h1302, h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                                        · linarith only [h1292, h1296, h1301, hc26, hlam, hphi, u6elo3]
                                  · linarith only [h1296, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1291, h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h1124, h1246, h1247, h1290, hc26, hlam, hphi, u6elo4]
                      · linarith only [h1124, h1246, h1287, hc26, hlam, hphi, u6elo3]
                · linarith only [h1246, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
        · linarith only [h0, h1123, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1378 | h1378
      · rcases m.htr 0 1 6 (by decide) (by decide) with h1379 | h1379
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1380 | h1380
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1381 | h1381
            · linarith only [h0, h1381, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1383 | h1383
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1384 | h1384
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1385 | h1385
                  · linarith only [h1, h1385, h2, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1387 | h1387
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1388 | h1388
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1389 | h1389
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1390 | h1390
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1391 | h1391
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1392 | h1392
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1393 | h1393
                                · linarith only [h0, h1381, h1393, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1395 | h1395
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1396 | h1396
                                    · linarith only [h0, h1, h1385, h1392, h1396, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                                    · linarith only [h0, h1392, h1396, h2, hc23, hc34, hlam, hphi]
                                  · linarith only [h1392, h1395, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1380, h1381, h1392, hc12, hc24, hlam, hphi]
                            · linarith only [h1391, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1390, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo4]
                        · linarith only [h1378, h1389, h2, hlam]
                      · linarith only [h1388, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1405 | h1405
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1406 | h1406
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1407 | h1407
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1408 | h1408
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1409 | h1409
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1410 | h1410
                                · linarith only [h0, h1381, h1410, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1412 | h1412
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1413 | h1413
                                    · linarith only [h1, h1385, h1413, hlam]
                                    · linarith only [h0, h1409, h1413, h2, hc23, hc34, hlam, hphi]
                                  · linarith only [h1409, h1412, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1380, h1381, h1409, hc12, hc24, hlam, hphi]
                            · linarith only [h1387, h1408, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                          · linarith only [h0, h1407, h2, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                        · linarith only [h1378, h1406, h2, hlam]
                      · linarith only [h1405, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h1380, h1384, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1423 | h1423
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1424 | h1424
                  · linarith only [h1, h1424, h2, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1426 | h1426
                    · linarith only [h1380, h1383, h1426, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1428 | h1428
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1429 | h1429
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1430 | h1430
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1431 | h1431
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1432 | h1432
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1433 | h1433
                                · linarith only [h0, h1381, h1433, h2, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1435 | h1435
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1436 | h1436
                                    · linarith only [h1, h1424, h1436, h2, hlam]
                                    · linarith only [h0, h1432, h1436, h2, hc23, hc34, hlam, hphi]
                                  · linarith only [h1432, h1435, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1380, h1383, h1432, hc12, hc25, hlam, hphi]
                            · linarith only [h1383, h1431, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h1430, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo4]
                        · linarith only [h1378, h1429, h2, hlam]
                      · linarith only [h1428, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h1380, h1423, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1446 | h1446
            · linarith only [h0, h1446, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1448 | h1448
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1449 | h1449
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1450 | h1450
                  · linarith only [h1, h1450, h2, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1452 | h1452
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1453 | h1453
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1454 | h1454
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1455 | h1455
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1456 | h1456
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1457 | h1457
                              · linarith only [h0, h1380, h1457, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1459 | h1459
                                · linarith only [h0, h1446, h1459, h2, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1461 | h1461
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1462 | h1462
                                    · linarith only [h1, h1450, h1459, h1462, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1464 | h1464
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1465 | h1465
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1466 | h1466
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1467 | h1467
                                            · linarith only [h1, h1457, h1462, h1467, h2, hc12, hc23, hlam, hphi]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1469 | h1469
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1470 | h1470
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1471 | h1471
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1472 | h1472
                                                    · linarith only [h1380, h1448, h1467, h1472, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                    · linarith only [h1471, h1472, hc45, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h1446, h1454, h1471, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                                · linarith only [h1470, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h1, h1378, h1380, h1448, h1459, h1464, h1466, h1467, h1469, h2, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h1466, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h1465, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h1, h1452, h1457, h1461, h1464, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                  · linarith only [h1461, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1456, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1455, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h1378, h1454, h2, hlam]
                      · linarith only [h1380, h1453, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                    · linarith only [h1380, h1448, h1452, hlam]
                · linarith only [h1448, h1449, hc25, hlam, hphi, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1488 | h1488
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1489 | h1489
                  · linarith only [h1, h1489, h2, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1491 | h1491
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1492 | h1492
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1493 | h1493
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1494 | h1494
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1495 | h1495
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1496 | h1496
                              · linarith only [h0, h1380, h1496, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1498 | h1498
                                · linarith only [h0, h1446, h1498, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1500 | h1500
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1501 | h1501
                                    · linarith only [h1, h1489, h1501, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1503 | h1503
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1504 | h1504
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1505 | h1505
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1506 | h1506
                                            · linarith only [h1, h1496, h1501, h1506, h2, hc12, hc23, hlam, hphi]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1508 | h1508
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1509 | h1509
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1510 | h1510
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1511 | h1511
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1512 | h1512
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1513 | h1513
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h1514 | h1514
                                                          · linarith only [h1, h1503, h1514, hc56, hlam, hphi, ht0b, ht6b, u0elo0]
                                                          · linarith only [h1514, hc35, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h1, h1498, h1506, h1513, h2, hc13, hc46, hlam, hphi, ht34]
                                                      · linarith only [h1, h1496, h1498, h1500, h1506, h1509, h1512, h2, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h0, h1448, h1500, h1509, h1511, hc36, hlam, hphi, u6elo5]
                                                  · linarith only [h1, h1491, h1493, h1496, h1498, h1500, h1509, h1510, h2, hc36, hlam, hphi, ht0b, ht6b, u0elo2]
                                                · linarith only [h1509, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h0, h1, h1380, h1498, h1500, h1503, h1506, h1508, h2, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h1505, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h1504, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h1491, h1496, h1500, h1503, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h1500, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1448, h1495, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h1494, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h1378, h1493, h2, hlam]
                      · linarith only [h1492, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1531 | h1531
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1532 | h1532
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1533 | h1533
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1534 | h1534
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1535 | h1535
                              · linarith only [h0, h1380, h1488, h1535, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1537 | h1537
                                · linarith only [h0, h1446, h1537, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1539 | h1539
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1540 | h1540
                                    · linarith only [h1, h1380, h1489, h1537, h1540, h2, hc02, hc24, hlam, hphi]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1542 | h1542
                                      · linarith only [h1, h1491, h1542, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1544 | h1544
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1545 | h1545
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1546 | h1546
                                            · linarith only [h1378, h1535, h1539, h1540, h1542, h1546, h2, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1548 | h1548
                                              · linarith only [h0, h1380, h1491, h1539, h1546, h1548, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1550 | h1550
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1551 | h1551
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1552 | h1552
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1553 | h1553
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1554 | h1554
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h1555 | h1555
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h1556 | h1556
                                                            · rcases h0bigk with h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h0, h1539, h1550, h1554, h1556, hc56, hlam, hphi, ht0b, ht6b, p1557_1, u0elo0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h0, h1380, h1537, h1539, h1550, h1554, h1556, h2, hc24, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p1557_1]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h2, hlam, p1557_1]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h0, h1380, h1491, h1537, h1539, h1550, h1554, h1556, h2, hc24, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p1557_1]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                rcases p1557_3 (m.d 0 1) (by simp) with h1563 | h1563
                                                                · rcases p1557_3 (m.d 0 2) (by simp) with h1564 | h1564
                                                                  · linarith only [h0, h1564, hlam]
                                                                  · linarith only [h1488, h1564, hlam]
                                                                · linarith only [h1379, h1563, hlam]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h0, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1380, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1446, hlam, p1557_1]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1448, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1379, h1380, h1548, h1553, hc16, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1557_1]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h0, h1491, h1539, h1550, h1554, h1556, hc56, hlam, hphi, ht0b, ht6b, p1557_1, u0elo4]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1489, hlam, p1557_1]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1491, hlam, p1557_1]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                rcases p1557_3 (m.d 0 1) (by simp) with h1579 | h1579
                                                                · rcases p1557_3 (m.d 0 2) (by simp) with h1580 | h1580
                                                                  · linarith only [h1380, h1580, hlam]
                                                                  · linarith only [h1488, h1580, hlam]
                                                                · linarith only [h1379, h1579, hlam]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h0, h1539, h1550, h1554, h1556, hc56, hlam, hphi, ht0b, ht6b, p1557_1, u0elo3]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h0, h1539, h1550, h1554, h1556, hc56, hlam, hphi, ht0b, ht6b, p1557_1, u0elo3]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1, h1535, h1539, h1550, h1554, h1556, hc56, hlam, hphi, ht0b, ht6b, p1557_1, u0elo3]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1378, h1535, h1539, h1542, h1550, h1554, h1556, hc56, hlam, hphi, ht0b, ht6b, p1557_1, u0elo3]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                rcases p1557_3 (m.d 0 1) (by simp) with h1589 | h1589
                                                                · linarith only [h1589, h2, hlam]
                                                                · linarith only [h1379, h1589, hlam]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1378, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h0, h1539, h1550, h1554, h1556, hc56, hlam, hphi, ht0b, ht6b, p1557_1, u0elo4]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1, h1378, h1535, h1537, h1539, h1546, h1550, h1554, h1556, h2, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1557_1]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1532, hlam, p1557_1]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                rcases p1557_3 (m.d 0 1) (by simp) with h1597 | h1597
                                                                · rcases p1557_3 (m.d 0 2) (by simp) with h1598 | h1598
                                                                  · linarith only [h1448, h1598, hlam]
                                                                  · linarith only [h1488, h1598, hlam]
                                                                · linarith only [h1379, h1597, hlam]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1379, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1488, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1531, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1533, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [h1534, hlam, p1557_0]
                                                              · obtain ⟨p1557_0, p1557_1, p1557_2, p1557_3⟩ := h1557c
                                                                linarith only [hlam, p1557_0]
                                                            · linarith only [h1556, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h1378, h1535, h1537, h1539, h1542, h1546, h1548, h1552, h1555, h2, hc23, hc34, hlam, hphi]
                                                        · linarith only [h1378, h1535, h1537, h1542, h1546, h1554, h2, hc12, hc46, hlam, hphi, ht23, ht34]
                                                      · linarith only [h1378, h1535, h1537, h1539, h1542, h1546, h1550, h1553, h2, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h0, h1380, h1539, h1548, h1550, h1552, hc36, hlam, hphi, u6elo5]
                                                  · linarith only [h1378, h1532, h1535, h1537, h1539, h1542, h1550, h1551, h2, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                                · linarith only [h1380, h1550, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h1535, h1539, h1542, h1545, hc26, hlam, hphi, u6elo5]
                                        · linarith only [h1535, h1539, h1544, hc26, hlam, hphi, u6elo3]
                                  · linarith only [h1539, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1534, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1533, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h1378, h1532, h2, hlam]
                      · linarith only [h1531, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h1488, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
        · linarith only [h1379, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h1624 | h1624
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1625 | h1625
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1626 | h1626
            · linarith only [h0, h1626, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1628 | h1628
              · linarith only [h0, h1378, h1628, hlam]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1630 | h1630
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1631 | h1631
                  · linarith only [h1, h1631, h2, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1633 | h1633
                    · linarith only [h0, h1378, h1625, h1633, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1635 | h1635
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1636 | h1636
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1637 | h1637
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1638 | h1638
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1639 | h1639
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1640 | h1640
                                · linarith only [h0, h1626, h1640, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1642 | h1642
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1643 | h1643
                                    · linarith only [h1, h1631, h1636, h1640, h1643, h2, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                    · linarith only [h0, h1639, h1643, h2, hc23, hc34, hlam, hphi]
                                  · linarith only [h1639, h1642, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1625, h1626, h1639, hc12, hc24, hlam, hphi]
                            · linarith only [h1378, h1638, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h0, h1378, h1625, h1636, h1637, hc23, hlam, hphi, ht34, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1650 | h1650
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1651 | h1651
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1652 | h1652
                              · linarith only [h0, h1636, h1652, h2, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h1625, h1626, h1652, hc12, hc24, hlam, hphi]
                            · linarith only [h1636, h1651, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h0, h1650, h2, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                      · linarith only [h1635, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h1625, h1630, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1659 | h1659
            · linarith only [h1, h1625, h1659, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1661 | h1661
              · linarith only [h1, h1378, h1625, h1661, hlam]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1663 | h1663
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1664 | h1664
                  · linarith only [h1, h1664, h2, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1666 | h1666
                    · linarith only [h1, h1378, h1666, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1668 | h1668
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1669 | h1669
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1670 | h1670
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1671 | h1671
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1672 | h1672
                              · linarith only [h0, h1625, h1672, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1674 | h1674
                                · linarith only [h0, h1378, h1659, h1669, h1674, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1676 | h1676
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1677 | h1677
                                    · linarith only [h1, h1664, h1674, h1677, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1679 | h1679
                                      · linarith only [h1, h1378, h1666, h1679, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1681 | h1681
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1682 | h1682
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1683 | h1683
                                            · linarith only [h1, h1672, h1677, h1683, h2, hc12, hc23, hlam, hphi]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1685 | h1685
                                              · linarith only [h1, h1378, h1672, h1676, h1679, h1683, h1685, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1687 | h1687
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1688 | h1688
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1689 | h1689
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1690 | h1690
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1691 | h1691
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h1692 | h1692
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h1693 | h1693
                                                            · rcases h0bigk with h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h0, h1676, h1687, h1691, h1693, hc56, hlam, hphi, ht0b, ht6b, p1694_1, u0elo0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h0, h1625, h1674, h1676, h1687, h1691, h1693, h2, hc24, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p1694_1]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h2, hlam, p1694_1]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1378, hlam, p1694_1]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                rcases p1694_3 (m.d 0 1) (by simp) with h1700 | h1700
                                                                · rcases p1694_3 (m.d 0 2) (by simp) with h1701 | h1701
                                                                  · linarith only [h0, h1701, hlam]
                                                                  · linarith only [h1663, h1701, hlam]
                                                                · linarith only [h1624, h1700, hlam]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h0, hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1625, hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1659, hlam, p1694_1]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1661, hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1624, h1625, h1685, h1690, hc16, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p1694_1]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1, hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h0, h1676, h1687, h1691, h1693, hc56, hlam, hphi, ht0b, ht6b, p1694_1, u0elo2]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1664, hlam, p1694_1]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1666, hlam, p1694_1]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                rcases p1694_3 (m.d 0 1) (by simp) with h1716 | h1716
                                                                · rcases p1694_3 (m.d 0 2) (by simp) with h1717 | h1717
                                                                  · linarith only [h1625, h1717, hlam]
                                                                  · linarith only [h1663, h1717, hlam]
                                                                · linarith only [h1624, h1716, hlam]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h0, h1676, h1687, h1691, h1693, hc56, hlam, hphi, ht0b, ht6b, p1694_1, u0elo3]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h0, h1676, h1687, h1691, h1693, hc56, hlam, hphi, ht0b, ht6b, p1694_1, u0elo3]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1, h1672, h1676, h1687, h1691, h1693, hc56, hlam, hphi, ht0b, ht6b, p1694_1, u0elo3]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1, h1378, h1672, h1676, h1687, h1691, h1693, hc56, hlam, hphi, ht0b, ht6b, p1694_1, u0elo3]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                rcases p1694_3 (m.d 0 1) (by simp) with h1726 | h1726
                                                                · linarith only [h1726, h2, hlam]
                                                                · linarith only [h1624, h1726, hlam]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1, h1672, h1676, h1687, h1691, h1693, hc56, hlam, hphi, ht0b, ht6b, p1694_1, u0elo4]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h0, h1676, h1687, h1691, h1693, hc56, hlam, hphi, ht0b, ht6b, p1694_1, u0elo4]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1, h1672, h1676, h1687, h1691, h1693, hc56, hlam, hphi, ht0b, ht6b, p1694_1, u0elo4]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1669, hlam, p1694_1]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                rcases p1694_3 (m.d 0 1) (by simp) with h1734 | h1734
                                                                · linarith only [h1378, h1734, hlam]
                                                                · linarith only [h1624, h1734, hlam]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1624, hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1663, hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1668, hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1670, hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [h1671, hlam, p1694_0]
                                                              · obtain ⟨p1694_0, p1694_1, p1694_2, p1694_3⟩ := h1694c
                                                                linarith only [hlam, p1694_0]
                                                            · linarith only [h1693, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h1, h1672, h1674, h1676, h1679, h1683, h1689, h1692, h2, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                        · linarith only [h1, h1672, h1674, h1683, h1691, h2, hc12, hc46, hlam, hphi, ht23, ht34]
                                                      · linarith only [h1, h1672, h1674, h1676, h1683, h1687, h1690, h2, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h1661, h1689, hc05, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h1, h1669, h1672, h1674, h1676, h1687, h1688, h2, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                                · linarith only [h1625, h1687, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h1, h1378, h1682, hc13, hc56, hlam, hphi, ht34, ht45]
                                        · linarith only [h1672, h1676, h1681, hc26, hlam, hphi, u6elo3]
                                  · linarith only [h1676, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h0, h1378, h1671, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h1670, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1755 | h1755
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1756 | h1756
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1757 | h1757
                              · linarith only [h0, h1625, h1663, h1757, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1759 | h1759
                                · linarith only [h0, h1659, h1759, h2, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1761 | h1761
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1762 | h1762
                                    · linarith only [h1, h1669, h1762, h2, hc34, hc45, hlam, hphi]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1764 | h1764
                                      · linarith only [h1, h1666, h1764, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1766 | h1766
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1767 | h1767
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1768 | h1768
                                            · linarith only [h0, h1761, h1762, h1768, h2, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1770 | h1770
                                              · linarith only [h1, h1378, h1757, h1761, h1764, h1770, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1772 | h1772
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1773 | h1773
                                                  · linarith only [h1, h1669, h1757, h1761, h1772, h1773, h2, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                  · linarith only [h1, h1757, h1759, h1761, h1772, h1773, h2, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                · linarith only [h1772, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h1, h1378, h1757, h1767, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                        · linarith only [h1757, h1761, h1766, hc26, hlam, hphi, u6elo3]
                                  · linarith only [h1761, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1756, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1755, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo4]
                      · linarith only [h1625, h1663, h1668, hc26, hlam, hphi, u6elo3]
                · linarith only [h1663, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
        · linarith only [h0, h1624, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1785 | h1785
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1786 | h1786
      · rcases m.htr 0 1 6 (by decide) (by decide) with h1787 | h1787
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1788 | h1788
          · linarith only [h0, h1, h1788, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1790 | h1790
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1791 | h1791
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1792 | h1792
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1793 | h1793
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1794 | h1794
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1795 | h1795
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1796 | h1796
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1797 | h1797
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1798 | h1798
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1799 | h1799
                              · linarith only [h0, h1788, h1799, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1801 | h1801
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1802 | h1802
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1803 | h1803
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1804 | h1804
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1805 | h1805
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1806 | h1806
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1807 | h1807
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1808 | h1808
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1809 | h1809
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1810 | h1810
                                                  · linarith only [h0, h1, h1799, h1801, h1810, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1812 | h1812
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1813 | h1813
                                                      · linarith only [h0, h1, h1799, h1801, h1807, h1810, h1813, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1815 | h1815
                                                        · linarith only [h0, h1, h1790, h1796, h1799, h1807, h1810, h1815, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                        · linarith only [h1815, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h1812, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h0, h1, h1799, h1809, hc12, hc36, hlam, hphi, ht23]
                                              · linarith only [h0, h1, h1799, h1801, h1807, h1808, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                            · linarith only [h0, h1, h1799, h1801, h1807, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                          · linarith only [h1806, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h0, h1, h1801, h1805, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                      · linarith only [h0, h1, h1801, h1804, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                    · linarith only [h0, h1, h1801, h1803, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                  · linarith only [h1801, h1802, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h0, h1, h1790, h1799, h1801, hc12, hc23, hlam, hphi]
                            · linarith only [h1798, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1797, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1830 | h1830
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1831 | h1831
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1832 | h1832
                              · linarith only [h0, h1, h1788, h1832, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1834 | h1834
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1835 | h1835
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1836 | h1836
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1837 | h1837
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1838 | h1838
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1839 | h1839
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1840 | h1840
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1841 | h1841
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1842 | h1842
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1843 | h1843
                                                  · linarith only [h1790, h1796, h1830, h1843, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1845 | h1845
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1846 | h1846
                                                      · linarith only [h1793, h1796, h1830, h1846, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1848 | h1848
                                                        · linarith only [h0, h1, h1832, h1834, h1840, h1848, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                        · linarith only [h1796, h1830, h1848, hc34, hc45, hlam, hphi]
                                                    · linarith only [h1841, h1845, hc35, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h0, h1, h1832, h1842, hc12, hc36, hlam, hphi, ht23]
                                              · linarith only [h0, h1, h1832, h1834, h1840, h1841, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                            · linarith only [h0, h1, h1832, h1834, h1840, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                          · linarith only [h1839, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h0, h1, h1834, h1838, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                      · linarith only [h0, h1, h1834, h1837, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                    · linarith only [h0, h1, h1834, h1836, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                  · linarith only [h1834, h1835, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h0, h1, h1790, h1832, h1834, hc12, hc23, hlam, hphi]
                            · linarith only [h1831, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1830, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h1795, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · linarith only [h1, h1786, h1794, hlam]
                  · linarith only [h1, h1785, h1793, hlam]
                · linarith only [h1790, h1792, hc24, hlam, hphi, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1867 | h1867
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1868 | h1868
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1869 | h1869
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1870 | h1870
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1871 | h1871
                        · linarith only [h1790, h1791, h1871, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1873 | h1873
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1874 | h1874
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1875 | h1875
                              · linarith only [h0, h1788, h1875, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1877 | h1877
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1878 | h1878
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1879 | h1879
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1880 | h1880
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1881 | h1881
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1882 | h1882
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1883 | h1883
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1884 | h1884
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1885 | h1885
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1886 | h1886
                                                  · linarith only [h0, h1, h1871, h1875, h1877, h1886, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1888 | h1888
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1889 | h1889
                                                      · linarith only [h0, h1791, h1877, h1883, h1886, h1889, hlam]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1891 | h1891
                                                        · linarith only [h0, h1, h1875, h1877, h1883, h1891, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                        · linarith only [h1891, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h1791, h1877, h1882, h1888, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                                · linarith only [h1, h1875, h1885, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h0, h1, h1875, h1877, h1883, h1884, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                            · linarith only [h0, h1, h1875, h1877, h1883, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                          · linarith only [h1882, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h0, h1, h1877, h1881, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                      · linarith only [h0, h1, h1877, h1880, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                    · linarith only [h0, h1, h1877, h1879, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                  · linarith only [h1877, h1878, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h1790, h1791, h1877, hc12, hc25, hlam, hphi]
                            · linarith only [h1791, h1874, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h1873, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h1, h1870, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                    · linarith only [h1, h1786, h1869, hlam]
                  · linarith only [h1, h1785, h1868, hlam]
                · linarith only [h1790, h1867, hc24, hlam, hphi, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1910 | h1910
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1911 | h1911
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1912 | h1912
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1913 | h1913
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1914 | h1914
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1915 | h1915
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1916 | h1916
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1917 | h1917
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1918 | h1918
                              · linarith only [h0, h1788, h1918, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1920 | h1920
                                · linarith only [h0, h1790, h1910, h1917, h1920, hc56, hlam, hphi, ht0b, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1922 | h1922
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1923 | h1923
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1924 | h1924
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1925 | h1925
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1926 | h1926
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1927 | h1927
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1928 | h1928
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1929 | h1929
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1930 | h1930
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1931 | h1931
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1932 | h1932
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1933 | h1933
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h1934 | h1934
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h1935 | h1935
                                                            · linarith only [h1, h1785, h1918, h1923, h1932, h1935, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                            · linarith only [h1910, h1928, h1934, h1935, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                                          · linarith only [h1931, h1934, hc35, hlam, hphi, ht56, u6elo2]
                                                        · linarith only [h1933, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1940 | h1940
                                                        · linarith only [h1, h1785, h1915, h1918, h1932, h1940, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                        · linarith only [h1940, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h1931, hc25, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h1790, h1915, h1930, hlam]
                                                · linarith only [h1, h1785, h1918, h1929, hc14, hlam, hphi, ht45, ht56, u6elo3]
                                              · linarith only [h1, h1785, h1918, h1920, h1922, h1928, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · linarith only [h1, h1785, h1918, h1920, h1922, h1927, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h1926, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h1, h1785, h1920, h1922, h1925, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                      · linarith only [h1, h1785, h1920, h1922, h1924, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h1, h1785, h1920, h1922, h1923, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h1922, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1917, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h1916, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h1790, h1910, h1915, hlam]
                      · linarith only [h1914, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · linarith only [h0, h1, h1910, h1913, hlam]
                  · linarith only [h1, h1785, h1912, hlam]
                · linarith only [h1911, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h1960 | h1960
                · rcases m.htr 0 3 4 (by decide) (by decide) with h1961 | h1961
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1962 | h1962
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1963 | h1963
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1964 | h1964
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1965 | h1965
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h1966 | h1966
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1967 | h1967
                              · linarith only [h0, h1788, h1960, h1967, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1969 | h1969
                                · linarith only [h0, h1790, h1969, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h1971 | h1971
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1972 | h1972
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1973 | h1973
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h1974 | h1974
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1975 | h1975
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1976 | h1976
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1977 | h1977
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1978 | h1978
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1979 | h1979
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h1980 | h1980
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1981 | h1981
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1982 | h1982
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h1983 | h1983
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h1984 | h1984
                                                            · linarith only [h1, h1785, h1967, h1972, h1981, h1984, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                            · linarith only [h1984, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h1971, h1980, h1983, hc35, hlam, hphi, ht56, u6elo1]
                                                        · linarith only [h1982, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h1989 | h1989
                                                        · linarith only [h1964, h1981, h1989, hc46, hlam, hphi, ht0b, ht6b, u0elo3]
                                                        · linarith only [h1989, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h1910, h1980, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                                                  · linarith only [h0, h1, h1785, h1790, h1964, h1967, h1971, h1978, h1979, hc23, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                · linarith only [h1, h1967, h1978, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h1, h1785, h1967, h1969, h1971, h1977, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · linarith only [h1, h1785, h1967, h1969, h1971, h1976, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h1975, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h1, h1785, h1969, h1971, h1974, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                      · linarith only [h1, h1785, h1969, h1971, h1973, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h1, h1785, h1969, h1971, h1972, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h1971, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1910, h1966, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h1910, h1960, h1964, h1965, hc26, hlam, hphi, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2004 | h2004
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2005 | h2005
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2006 | h2006
                              · linarith only [h0, h1, h1788, h2006, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2008 | h2008
                                · linarith only [h0, h1790, h2008, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2010 | h2010
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2011 | h2011
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2012 | h2012
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2013 | h2013
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2014 | h2014
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2015 | h2015
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2016 | h2016
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2017 | h2017
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2018 | h2018
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2019 | h2019
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2020 | h2020
                                                      · linarith only [h1785, h1964, h2011, h2020, hlam]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2022 | h2022
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2023 | h2023
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2024 | h2024
                                                            · rcases h0bigk with h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h0, h1, h2006, h2010, h2017, h2022, h2024, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2025_1]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1, hlam, p2025_1]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1, h1785, h2006, h2008, h2010, h2017, h2022, h2024, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2025_1]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1, h1785, h1964, h2006, h2008, h2010, h2017, h2022, h2024, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2025_1]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                rcases p2025_3 (m.d 0 1) (by simp) with h2031 | h2031
                                                                · rcases p2025_3 (m.d 0 2) (by simp) with h2032 | h2032
                                                                  · linarith only [h0, h2032, hlam]
                                                                  · linarith only [h1960, h2032, hlam]
                                                                · linarith only [h1787, h2031, hlam]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h0, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1788, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1790, hlam, p2025_1]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1910, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1790, h1964, h2018, hc06, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, p2025_1]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h0, h2010, h2017, h2022, h2024, hc56, hlam, hphi, ht0b, ht6b, p2025_1, u0elo2]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h0, h2010, h2017, h2022, h2024, hc56, hlam, hphi, ht0b, ht6b, p2025_1, u0elo2]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1785, h2008, h2010, h2017, h2022, h2024, hc56, hlam, hphi, ht0b, ht6b, p2025_1, u0elo2]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1786, h2012, h2020, h2022, h2024, hc56, hlam, hphi, ht0b, ht6b, p2025_1, u0elo2]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                rcases p2025_3 (m.d 0 1) (by simp) with h2047 | h2047
                                                                · linarith only [h1, h2047, hlam]
                                                                · linarith only [h1787, h2047, hlam]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1785, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h0, h2010, h2017, h2022, h2024, hc56, hlam, hphi, ht0b, ht6b, p2025_1, u0elo3]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1961, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1964, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1787, h1964, h2010, h2015, h2017, h2018, h2022, h2024, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2025_1]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1786, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h0, h1786, h2010, h2017, h2022, h2024, hc56, hlam, hphi, ht0b, ht6b, p2025_1, u0elo0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1962, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1, h1785, h1786, h2006, h2008, h2010, h2017, h2022, h2024, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2025_1]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                rcases p2025_3 (m.d 0 1) (by simp) with h2061 | h2061
                                                                · rcases p2025_3 (m.d 0 2) (by simp) with h2062 | h2062
                                                                  · linarith only [h1910, h2062, hlam]
                                                                  · linarith only [h1960, h2062, hlam]
                                                                · linarith only [h1787, h2061, hlam]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1787, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1960, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h1963, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h2004, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [h2005, hlam, p2025_0]
                                                              · obtain ⟨p2025_0, p2025_1, p2025_2, p2025_3⟩ := h2025c
                                                                linarith only [hlam, p2025_0]
                                                            · linarith only [h2024, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h1785, h2008, h2010, h2019, h2020, h2022, h2023, hc46, hlam, hphi, ht0b, ht6b, u0elo3]
                                                        · linarith only [h2022, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h1790, h1964, h2010, h2014, h2018, h2019, hc15, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2076 | h2076
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2077 | h2077
                                                      · linarith only [h0, h1790, h2010, h2017, h2018, h2077, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2079 | h2079
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2080 | h2080
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2081 | h2081
                                                            · rcases h0bigk with h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h2010, h2017, h2079, h2081, hc56, hlam, hphi, ht0b, ht6b, p2082_1, u0elo0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1, hlam, p2082_1]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h1, h1790, h2006, h2010, h2017, h2079, h2081, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2082_1]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h1, h1910, h2006, h2010, h2017, h2079, h2081, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2082_1]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                rcases p2082_3 (m.d 0 1) (by simp) with h2088 | h2088
                                                                · rcases p2082_3 (m.d 0 2) (by simp) with h2089 | h2089
                                                                  · linarith only [h0, h2089, hlam]
                                                                  · linarith only [h1960, h2089, hlam]
                                                                · linarith only [h1787, h2088, hlam]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1788, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1790, hlam, p2082_1]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1910, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1787, h1790, h2018, hc16, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p2082_1]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h2010, h2017, h2079, h2081, hc56, hlam, hphi, ht0b, ht6b, p2082_1, u0elo2]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h2010, h2017, h2079, h2081, hc56, hlam, hphi, ht0b, ht6b, p2082_1, u0elo2]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h1790, h2010, h2017, h2079, h2081, hc56, hlam, hphi, ht0b, ht6b, p2082_1, u0elo2]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h1790, h1964, h2010, h2017, h2079, h2081, hc56, hlam, hphi, ht0b, ht6b, p2082_1, u0elo2]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                rcases p2082_3 (m.d 0 1) (by simp) with h2104 | h2104
                                                                · linarith only [h1, h2104, hlam]
                                                                · linarith only [h1787, h2104, hlam]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1785, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h2010, h2017, h2079, h2081, hc56, hlam, hphi, ht0b, ht6b, p2082_1, u0elo3]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1961, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1964, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                rcases p2082_3 (m.d 0 1) (by simp) with h2112 | h2112
                                                                · rcases p2082_3 (m.d 0 2) (by simp) with h2113 | h2113
                                                                  · linarith only [h1790, h2113, hlam]
                                                                  · linarith only [h1960, h2113, hlam]
                                                                · linarith only [h1787, h2112, hlam]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1786, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h1, h1786, h2006, h2010, h2017, h2079, h2081, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2082_1]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1962, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h0, h1, h1786, h1790, h2006, h2010, h2017, h2079, h2081, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2082_1]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                rcases p2082_3 (m.d 0 1) (by simp) with h2122 | h2122
                                                                · rcases p2082_3 (m.d 0 2) (by simp) with h2123 | h2123
                                                                  · linarith only [h1910, h2123, hlam]
                                                                  · linarith only [h1960, h2123, hlam]
                                                                · linarith only [h1787, h2122, hlam]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1787, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1960, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h1963, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h2004, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [h2005, hlam, p2082_0]
                                                              · obtain ⟨p2082_0, p2082_1, p2082_2, p2082_3⟩ := h2082c
                                                                linarith only [hlam, p2082_0]
                                                            · linarith only [h2018, h2081, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                                          · linarith only [h0, h1790, h2010, h2018, h2076, h2080, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b]
                                                        · linarith only [h2079, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h1790, h2018, h2076, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                                                · linarith only [h1, h1785, h2006, h2008, h2017, hc12, hc36, hlam, hphi, ht23]
                                              · linarith only [h1, h1785, h2006, h2008, h2010, h2016, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · linarith only [h1, h1785, h2006, h2008, h2010, h2015, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h2014, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h1, h1785, h2008, h2010, h2013, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                      · linarith only [h1, h1785, h2008, h2010, h2012, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h1, h1785, h2008, h2010, h2011, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h2010, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1790, h1964, h2005, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h1790, h1960, h2004, hc26, hlam, hphi, u6elo4]
                      · linarith only [h1963, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · linarith only [h1, h1786, h1962, hlam]
                  · linarith only [h1, h1785, h1961, hlam]
                · linarith only [h1960, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
        · linarith only [h1787, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h2152 | h2152
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2153 | h2153
          · linarith only [h0, h1, h2153, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2155 | h2155
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2156 | h2156
              · linarith only [h0, h1786, h2156, hlam]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h2158 | h2158
                · rcases m.htr 0 3 4 (by decide) (by decide) with h2159 | h2159
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2160 | h2160
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2161 | h2161
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2162 | h2162
                        · linarith only [h0, h1786, h2155, h2162, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2164 | h2164
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2165 | h2165
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2166 | h2166
                              · linarith only [h0, h2153, h2166, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2168 | h2168
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2169 | h2169
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2170 | h2170
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2171 | h2171
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2172 | h2172
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2173 | h2173
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2174 | h2174
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2175 | h2175
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2176 | h2176
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2177 | h2177
                                                  · linarith only [h0, h1786, h2162, h2166, h2168, h2171, h2177, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2179 | h2179
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2180 | h2180
                                                      · linarith only [h2156, h2159, h2177, h2180, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2182 | h2182
                                                        · linarith only [h0, h1786, h2166, h2168, h2171, h2174, h2182, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                        · linarith only [h2182, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h1786, h2156, h2168, h2179, hc24, hc56, hlam, hphi, ht45]
                                                · linarith only [h0, h1786, h2166, h2168, h2171, h2174, h2176, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                              · linarith only [h0, h1786, h2166, h2168, h2171, h2174, h2175, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                            · linarith only [h0, h1786, h2166, h2171, h2174, hc12, hc34, hlam, hphi, ht23]
                                          · linarith only [h0, h1786, h2168, h2173, hc24, hc56, hlam, hphi, ht45]
                                        · linarith only [h0, h1786, h2168, h2171, h2172, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                      · linarith only [h0, h1, h2160, h2168, h2171, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                    · linarith only [h0, h1, h2168, h2170, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                  · linarith only [h2168, h2169, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h0, h1, h2155, h2166, h2168, hc12, hc23, hlam, hphi]
                            · linarith only [h1786, h2165, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h2164, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h2161, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2198 | h2198
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2199 | h2199
                        · linarith only [h1, h1785, h2160, h2199, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2201 | h2201
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2202 | h2202
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2203 | h2203
                              · linarith only [h0, h1, h2160, h2203, hc23, hc35, hlam, hphi]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2205 | h2205
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2206 | h2206
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2207 | h2207
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2208 | h2208
                                      · linarith only [h0, h1, h2160, h2205, h2208, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                      · linarith only [h0, h1, h2205, h2208, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                    · linarith only [h0, h1, h2205, h2207, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                  · linarith only [h2205, h2206, hc24, hlam, hphi, ht45, ht56, u6elo2]
                                · linarith only [h2153, h2155, h2205, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h2160, h2202, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h2201, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h0, h1, h2198, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                  · linarith only [h1, h1785, h2159, hlam]
                · linarith only [h2155, h2158, hc24, hlam, hphi, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2219 | h2219
              · linarith only [h0, h1786, h2219, hlam]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h2221 | h2221
                · rcases m.htr 0 3 4 (by decide) (by decide) with h2222 | h2222
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2223 | h2223
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2224 | h2224
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2225 | h2225
                        · linarith only [h1785, h1786, h2225, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2227 | h2227
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2228 | h2228
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2229 | h2229
                              · linarith only [h0, h2153, h2229, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2231 | h2231
                                · linarith only [h0, h2155, h2231, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2233 | h2233
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2234 | h2234
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2235 | h2235
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2236 | h2236
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2237 | h2237
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2238 | h2238
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2239 | h2239
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2240 | h2240
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2241 | h2241
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2242 | h2242
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2243 | h2243
                                                      · linarith only [h1785, h1786, h2225, h2234, h2243, hlam]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2245 | h2245
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2246 | h2246
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2247 | h2247
                                                            · rcases h0bigk with h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h1786, h2225, h2238, h2241, hc02, hc23, hlam, hphi, p2248_1]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h1, hlam, p2248_1]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h0, h1786, h2155, h2225, h2238, h2241, hc12, hc23, hlam, hphi, p2248_1]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h1786, hlam, p2248_1]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                rcases p2248_3 (m.d 0 1) (by simp) with h2254 | h2254
                                                                · rcases p2248_3 (m.d 0 2) (by simp) with h2255 | h2255
                                                                  · linarith only [h0, h2255, hlam]
                                                                  · linarith only [h2221, h2255, hlam]
                                                                · linarith only [h2152, h2254, hlam]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h0, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2153, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2155, hlam, p2248_1]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2219, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2155, h2221, h2225, h2238, h2240, h2241, h2245, h2247, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2248_1]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h1785, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p2248_1, u0elo2]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h0, h2233, h2240, h2245, h2247, hc56, hlam, hphi, ht0b, ht6b, p2248_1, u0elo2]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h0, h2155, h2233, h2240, h2245, h2247, hc56, hlam, hphi, ht0b, ht6b, p2248_1, u0elo2]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h0, h1786, h2233, h2240, h2245, h2247, hc56, hlam, hphi, ht0b, ht6b, p2248_1, u0elo2]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                rcases p2248_3 (m.d 0 1) (by simp) with h2270 | h2270
                                                                · linarith only [h1, h2270, hlam]
                                                                · linarith only [h2152, h2270, hlam]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h1785, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h0, h2233, h2240, h2245, h2247, hc56, hlam, hphi, ht0b, ht6b, p2248_1, u0elo3]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2222, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2225, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2152, h2225, h2233, h2238, h2240, h2241, h2245, h2247, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2248_1]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h0, h2233, h2240, h2245, h2247, hc56, hlam, hphi, ht0b, ht6b, p2248_1, u0elo4]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h0, h2233, h2240, h2245, h2247, hc56, hlam, hphi, ht0b, ht6b, p2248_1, u0elo4]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2223, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h1785, h2223, h2231, h2233, h2240, h2245, h2247, hc56, hlam, hphi, ht0b, ht6b, p2248_1, u0elo2]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                rcases p2248_3 (m.d 0 1) (by simp) with h2284 | h2284
                                                                · linarith only [h1786, h2284, hlam]
                                                                · linarith only [h2152, h2284, hlam]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2152, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2221, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2224, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2227, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [h2228, hlam, p2248_0]
                                                              · obtain ⟨p2248_0, p2248_1, p2248_2, p2248_3⟩ := h2248c
                                                                linarith only [hlam, p2248_0]
                                                            · linarith only [h2225, h2247, hc05, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h1785, h1786, h2225, h2231, h2233, h2238, h2241, h2242, h2246, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                        · linarith only [h2245, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h1786, h2225, h2241, h2242, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2297 | h2297
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2298 | h2298
                                                      · linarith only [h2155, h2241, h2298, hc02, hc34, hlam, hphi, ht23]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2300 | h2300
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2301 | h2301
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2302 | h2302
                                                            · rcases h0bigk with h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c | h2303c
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h0, h2233, h2240, h2300, h2302, hc56, hlam, hphi, ht0b, ht6b, p2303_1, u0elo0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h1, hlam, p2303_1]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h1785, h1786, h2229, h2231, h2233, h2235, h2240, h2300, h2302, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p2303_1]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h1786, hlam, p2303_1]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                rcases p2303_3 (m.d 0 1) (by simp) with h2309 | h2309
                                                                · rcases p2303_3 (m.d 0 2) (by simp) with h2310 | h2310
                                                                  · linarith only [h0, h2310, hlam]
                                                                  · linarith only [h2221, h2310, hlam]
                                                                · linarith only [h2152, h2309, hlam]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h0, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2153, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2155, hlam, p2303_1]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2219, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2152, h2155, h2233, h2240, h2241, h2300, h2302, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p2303_1]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h0, h2233, h2240, h2300, h2302, hc56, hlam, hphi, ht0b, ht6b, p2303_1, u0elo2]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h0, h2233, h2240, h2300, h2302, hc56, hlam, hphi, ht0b, ht6b, p2303_1, u0elo2]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h1785, h2231, h2233, h2240, h2300, h2302, hc56, hlam, hphi, ht0b, ht6b, p2303_1, u0elo2]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h1785, h1786, h2231, h2233, h2240, h2300, h2302, hc56, hlam, hphi, ht0b, ht6b, p2303_1, u0elo2]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                rcases p2303_3 (m.d 0 1) (by simp) with h2325 | h2325
                                                                · linarith only [h1, h2325, hlam]
                                                                · linarith only [h2152, h2325, hlam]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h1785, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h0, h2233, h2240, h2300, h2302, hc56, hlam, hphi, ht0b, ht6b, p2303_1, u0elo3]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2222, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2225, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                rcases p2303_3 (m.d 0 1) (by simp) with h2333 | h2333
                                                                · rcases p2303_3 (m.d 0 2) (by simp) with h2334 | h2334
                                                                  · linarith only [h2155, h2334, hlam]
                                                                  · linarith only [h2221, h2334, hlam]
                                                                · linarith only [h2152, h2333, hlam]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h0, h2233, h2240, h2300, h2302, hc56, hlam, hphi, ht0b, ht6b, p2303_1, u0elo4]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h0, h2233, h2240, h2300, h2302, hc56, hlam, hphi, ht0b, ht6b, p2303_1, u0elo4]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2223, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h1785, h2223, h2231, h2233, h2240, h2300, h2302, hc56, hlam, hphi, ht0b, ht6b, p2303_1, u0elo2]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                rcases p2303_3 (m.d 0 1) (by simp) with h2343 | h2343
                                                                · linarith only [h1786, h2343, hlam]
                                                                · linarith only [h2152, h2343, hlam]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2152, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2221, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2224, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2227, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [h2228, hlam, p2303_0]
                                                              · obtain ⟨p2303_0, p2303_1, p2303_2, p2303_3⟩ := h2303c
                                                                linarith only [hlam, p2303_0]
                                                            · linarith only [h2241, h2302, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                                          · linarith only [h0, h2155, h2233, h2241, h2297, h2298, h2301, hc34, hc45, hlam, hphi]
                                                        · linarith only [h2300, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h2219, h2297, hc05, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h1785, h1786, h2229, h2231, h2235, h2240, hc12, hc36, hlam, hphi, ht23]
                                              · linarith only [h1785, h1786, h2229, h2231, h2235, h2239, hc12, hc35, hlam, hphi, ht23]
                                            · linarith only [h1785, h1786, h2229, h2231, h2233, h2235, h2238, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h1785, h1786, h2231, h2233, h2237, hc26, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b]
                                        · linarith only [h1785, h1786, h2231, h2233, h2235, h2236, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                      · linarith only [h1, h1785, h2223, h2231, h2233, h2235, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                    · linarith only [h1, h1785, h2231, h2233, h2234, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h2233, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h2228, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h2155, h2221, h2227, hc26, hlam, hphi, u6elo4]
                      · linarith only [h2224, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2367 | h2367
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2368 | h2368
                        · linarith only [h1, h1785, h2223, h2368, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2370 | h2370
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2371 | h2371
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2372 | h2372
                              · linarith only [h0, h2153, h2221, h2372, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2374 | h2374
                                · linarith only [h0, h1, h2155, h2223, h2374, hc02, hc35, hlam, hphi, ht23]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2376 | h2376
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2377 | h2377
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2378 | h2378
                                      · linarith only [h0, h1, h2223, h2372, h2376, h2378, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                      · linarith only [h1, h1785, h2374, h2376, h2378, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h1, h1785, h2374, h2376, h2377, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h2376, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h2371, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h2155, h2370, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                      · linarith only [h0, h1, h2367, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                  · linarith only [h1, h1785, h2222, hlam]
                · linarith only [h2221, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
        · linarith only [h0, h2152, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2389 | h2389
      · rcases m.htr 0 1 6 (by decide) (by decide) with h2390 | h2390
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2391 | h2391
          · linarith only [h0, h1, h2391, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2393 | h2393
            · linarith only [h0, h1785, h2393, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2395 | h2395
              · rcases m.htr 0 2 6 (by decide) (by decide) with h2396 | h2396
                · rcases m.htr 0 3 4 (by decide) (by decide) with h2397 | h2397
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2398 | h2398
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2399 | h2399
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2400 | h2400
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2401 | h2401
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2402 | h2402
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2403 | h2403
                              · linarith only [h0, h2391, h2403, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2405 | h2405
                                · linarith only [h0, h1785, h2393, h2405, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2407 | h2407
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2408 | h2408
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2409 | h2409
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2410 | h2410
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2411 | h2411
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2412 | h2412
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2413 | h2413
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2414 | h2414
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2415 | h2415
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2416 | h2416
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2417 | h2417
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2418 | h2418
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2419 | h2419
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2420 | h2420
                                                            · linarith only [h2397, h2417, h2420, hc56, hlam, hphi, ht0b, ht6b, u0elo2]
                                                            · linarith only [h2420, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h0, h1785, h2395, h2403, h2408, h2416, h2419, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                        · linarith only [h2418, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2425 | h2425
                                                        · linarith only [h2400, h2417, h2425, hc46, hlam, hphi, ht0b, ht6b, u0elo3]
                                                        · linarith only [h2425, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h2416, hc25, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h0, h1785, h2405, h2415, hc12, hc45, hlam, hphi, ht23, ht34]
                                                · linarith only [h0, h1785, h2403, h2407, h2408, h2414, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                              · linarith only [h0, h1785, h2403, h2407, h2408, h2413, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · linarith only [h0, h1785, h2403, h2407, h2408, h2412, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h2409, h2411, hc35, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h0, h1785, h2407, h2408, h2410, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                      · linarith only [h0, h1785, h2407, h2408, h2409, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h0, h1, h2397, h2407, h2408, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h2407, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h2402, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h2401, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h1785, h2389, h2400, hlam]
                      · linarith only [h2399, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · linarith only [h0, h1785, h2395, h2397, h2398, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2443 | h2443
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2444 | h2444
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2445 | h2445
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2446 | h2446
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2447 | h2447
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2448 | h2448
                              · linarith only [h0, h2391, h2448, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2450 | h2450
                                · linarith only [h0, h2393, h2450, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2452 | h2452
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2453 | h2453
                                    · linarith only [h0, h1, h2397, h2452, h2453, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                    · linarith only [h0, h1, h2452, h2453, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h2452, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h2447, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h0, h1, h2397, h2446, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                        · linarith only [h1, h2389, h2397, h2445, hlam]
                      · linarith only [h0, h1, h2444, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                    · linarith only [h0, h1, h2395, h2443, hlam]
                · linarith only [h2396, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h2463 | h2463
                · rcases m.htr 0 3 4 (by decide) (by decide) with h2464 | h2464
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2465 | h2465
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2466 | h2466
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2467 | h2467
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2468 | h2468
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2469 | h2469
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2470 | h2470
                              · linarith only [h0, h2391, h2470, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2472 | h2472
                                · linarith only [h0, h2393, h2472, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2474 | h2474
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2475 | h2475
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2476 | h2476
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2477 | h2477
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2478 | h2478
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2479 | h2479
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2480 | h2480
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2481 | h2481
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2482 | h2482
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2483 | h2483
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2484 | h2484
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2485 | h2485
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2486 | h2486
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2487 | h2487
                                                            · linarith only [h2464, h2484, h2487, hc56, hlam, hphi, ht0b, ht6b, u0elo2]
                                                            · linarith only [h2487, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h0, h2474, h2483, h2486, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                                        · linarith only [h2485, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2492 | h2492
                                                        · linarith only [h2464, h2467, h2484, h2492, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                                        · linarith only [h2492, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h2395, h2483, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                                                  · linarith only [h0, h1785, h2464, h2467, h2472, h2474, h2481, h2482, hc36, hlam, hphi, ht0b, ht6b, u0elo2]
                                                · linarith only [h0, h1785, h2470, h2475, h2481, hc12, hc36, hlam, hphi, ht23]
                                              · linarith only [h0, h1785, h2470, h2474, h2475, h2480, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · linarith only [h0, h1785, h2470, h2474, h2475, h2479, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h2478, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h0, h1785, h2474, h2475, h2477, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                      · linarith only [h0, h1785, h2474, h2475, h2476, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h0, h1, h2464, h2474, h2475, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h2474, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h2395, h2469, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h2468, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h1785, h2389, h2467, hlam]
                      · linarith only [h2466, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · linarith only [h1785, h2389, h2464, h2465, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2510 | h2510
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2511 | h2511
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2512 | h2512
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2513 | h2513
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2514 | h2514
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2515 | h2515
                              · linarith only [h0, h2391, h2463, h2515, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2517 | h2517
                                · linarith only [h0, h2393, h2463, h2517, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2519 | h2519
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2520 | h2520
                                    · linarith only [h0, h1, h2464, h2515, h2519, h2520, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                    · linarith only [h0, h1, h2519, h2520, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h2519, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h2395, h2514, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h2513, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h1, h2389, h2464, h2512, hlam]
                      · linarith only [h0, h1, h2511, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                    · linarith only [h1, h2389, h2510, hlam]
                · linarith only [h2463, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
        · linarith only [h0, h2390, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h2531 | h2531
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2532 | h2532
          · linarith only [h0, h1, h2532, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2534 | h2534
            · linarith only [h0, h1785, h2534, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2536 | h2536
              · linarith only [h0, h2389, h2536, hlam]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h2538 | h2538
                · rcases m.htr 0 3 4 (by decide) (by decide) with h2539 | h2539
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2540 | h2540
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2541 | h2541
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2542 | h2542
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2543 | h2543
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2544 | h2544
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2545 | h2545
                              · linarith only [h0, h2532, h2545, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2547 | h2547
                                · linarith only [h0, h2389, h2534, h2542, h2547, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2549 | h2549
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2550 | h2550
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2551 | h2551
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2552 | h2552
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2553 | h2553
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2554 | h2554
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2555 | h2555
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2556 | h2556
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2557 | h2557
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2558 | h2558
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2559 | h2559
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2560 | h2560
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2561 | h2561
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2562 | h2562
                                                            · linarith only [h2539, h2559, h2562, hc56, hlam, hphi, ht0b, ht6b, u0elo2]
                                                            · linarith only [h2562, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h0, h2549, h2558, h2561, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                                        · linarith only [h2560, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2567 | h2567
                                                        · linarith only [h2539, h2542, h2559, h2567, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                                        · linarith only [h2567, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h2536, h2558, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                                                  · linarith only [h0, h2534, h2539, h2542, h2549, h2556, h2557, hc36, hlam, hphi, ht0b, ht6b, u0elo2]
                                                · linarith only [h1785, h2545, h2550, h2556, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h0, h1785, h2545, h2549, h2550, h2555, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · linarith only [h0, h1785, h2545, h2549, h2550, h2554, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h0, h2389, h2549, h2553, hc26, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b]
                                        · linarith only [h0, h1785, h2549, h2550, h2552, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                      · linarith only [h0, h1785, h2540, h2549, h2550, h2551, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                    · linarith only [h0, h1, h2539, h2549, h2550, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h2549, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h2544, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h2543, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2582 | h2582
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2583 | h2583
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2584 | h2584
                              · linarith only [h0, h1785, h2532, h2542, h2584, hc03, hc45, hlam, hphi, ht34]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2586 | h2586
                                · linarith only [h0, h1785, h2534, h2586, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2588 | h2588
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2589 | h2589
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2590 | h2590
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2591 | h2591
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2592 | h2592
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2593 | h2593
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2594 | h2594
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2595 | h2595
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2596 | h2596
                                                  · linarith only [h0, h1785, h2542, h2588, h2595, h2596, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                  · linarith only [h0, h1785, h2586, h2588, h2595, h2596, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                · linarith only [h0, h1785, h2584, h2589, h2595, hc12, hc36, hlam, hphi, ht23]
                                              · linarith only [h0, h1785, h2540, h2584, h2588, h2589, h2594, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                            · linarith only [h0, h1785, h2539, h2584, h2588, h2589, h2593, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                          · linarith only [h0, h2389, h2588, h2592, hc26, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b]
                                        · linarith only [h0, h1785, h2588, h2589, h2591, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                      · linarith only [h0, h1785, h2540, h2588, h2589, h2590, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                    · linarith only [h0, h1, h2539, h2588, h2589, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h2588, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1785, h2542, h2583, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h0, h1785, h2582, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                      · linarith only [h2541, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2610 | h2610
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2611 | h2611
                        · linarith only [h2539, h2540, h2611, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2613 | h2613
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2614 | h2614
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2615 | h2615
                              · linarith only [h0, h2532, h2615, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2617 | h2617
                                · linarith only [h0, h1785, h2534, h2617, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2619 | h2619
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2620 | h2620
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2621 | h2621
                                      · linarith only [h0, h1785, h2539, h2540, h2615, h2621, hc12, hc23, hlam, hphi]
                                      · linarith only [h0, h1, h2619, h2621, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h0, h1, h2539, h2619, h2620, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h2619, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h2614, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h0, h1785, h2613, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                      · linarith only [h2610, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2629 | h2629
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2630 | h2630
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2631 | h2631
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2632 | h2632
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2633 | h2633
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2634 | h2634
                              · linarith only [h0, h2389, h2539, h2629, h2634, hc23, hc34, hlam, hphi]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2636 | h2636
                                · linarith only [h0, h2534, h2636, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2638 | h2638
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2639 | h2639
                                    · linarith only [h0, h2389, h2539, h2629, h2634, h2639, hc12, hc23, hlam, hphi]
                                    · linarith only [h0, h1, h2638, h2639, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h2638, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h0, h2389, h2633, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h0, h2389, h2539, h2629, h2632, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                        · linarith only [h2539, h2629, h2631, hlam]
                      · linarith only [h0, h2389, h2629, h2630, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2647 | h2647
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2648 | h2648
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2649 | h2649
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2650 | h2650
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2651 | h2651
                              · linarith only [h0, h1, h2629, h2651, hc23, hc35, hlam, hphi]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2653 | h2653
                                · linarith only [h0, h2534, h2653, hlam]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2655 | h2655
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2656 | h2656
                                    · linarith only [h0, h1, h2539, h2655, h2656, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                    · linarith only [h0, h1, h2655, h2656, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h2655, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1, h2629, h2650, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h0, h1, h2629, h2648, h2649, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2662 | h2662
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2663 | h2663
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2664 | h2664
                              · linarith only [h0, h1, h2629, h2664, hc23, hc35, hlam, hphi]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2666 | h2666
                                · linarith only [h0, h1, h2539, h2648, h2666, hc24, hc45, hlam, hphi]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2668 | h2668
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2669 | h2669
                                    · linarith only [h0, h1, h2539, h2668, h2669, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                    · linarith only [h0, h1, h2668, h2669, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · linarith only [h2668, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h1, h2539, h2648, h2663, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h0, h1, h2539, h2662, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                      · linarith only [h0, h1, h2647, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                · linarith only [h2538, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
        · linarith only [h0, h2531, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo1]

set_option maxHeartbeats 5798000 in
private theorem n8l_sBT8_M_LI_H_L_s2 (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2678 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h6elo := hb6.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  have h0 := hg0
  have h2678 := hg2678
  rcases m.htr 0 1 4 (by decide) (by decide) with h3738 | h3738
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3739 | h3739
    · rcases m.htr 0 1 6 (by decide) (by decide) with h3740 | h3740
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3741 | h3741
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3742 | h3742
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3743 | h3743
            · rcases m.htr 0 2 6 (by decide) (by decide) with h3744 | h3744
              · rcases m.htr 0 3 4 (by decide) (by decide) with h3745 | h3745
                · rcases m.htr 0 3 5 (by decide) (by decide) with h3746 | h3746
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h3747 | h3747
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h3748 | h3748
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h3749 | h3749
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h3750 | h3750
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h3751 | h3751
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h3752 | h3752
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h3753 | h3753
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h3754 | h3754
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3755 | h3755
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h3756 | h3756
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h3757 | h3757
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3758 | h3758
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3759 | h3759
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h3760 | h3760
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3761 | h3761
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h3762 | h3762
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3763 | h3763
                                                    · linarith only [h3741, h3758, h3763, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                                    · linarith only [h3738, h3752, h3761, h3763, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                                  · linarith only [h3762, hc25, hlam, hphi, ht56, u6elo5]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h3767 | h3767
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3768 | h3768
                                                    · linarith only [h3741, h3758, h3761, h3768, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h3770 | h3770
                                                      · linarith only [h2678, h3738, h3748, h3751, h3758, h3761, h3770, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                      · linarith only [h3770, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h3767, hc25, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h3760, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h3746, h3758, h3759, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3776 | h3776
                                            · linarith only [h2678, h3738, h3751, h3754, h3758, h3776, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h3778 | h3778
                                              · linarith only [h2678, h3738, h3751, h3754, h3758, h3778, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h3778, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h3757, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h3756, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h3746, h3755, hlam]
                                  · linarith only [h2678, h3745, h3754, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                · linarith only [h3753, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3742, h3752, hlam]
                            · linarith only [h0, h3741, h3751, hlam]
                          · linarith only [h3750, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h3749, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h3790 | h3790
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h3791 | h3791
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h3792 | h3792
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h3793 | h3793
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h3794 | h3794
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h3795 | h3795
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3796 | h3796
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h3797 | h3797
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h3798 | h3798
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3799 | h3799
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3800 | h3800
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h3801 | h3801
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3802 | h3802
                                                · linarith only [h3738, h3748, h3790, h3793, h3802, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h3804 | h3804
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3805 | h3805
                                                    · linarith only [h3748, h3790, h3799, h3805, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h3807 | h3807
                                                      · linarith only [h3741, h3799, h3807, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                      · linarith only [h3807, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h3802, h3804, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                              · linarith only [h3801, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h3741, h3746, h3799, h3800, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3813 | h3813
                                            · linarith only [h2678, h3738, h3741, h3795, h3799, h3813, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h3815 | h3815
                                              · linarith only [h2678, h3738, h3741, h3795, h3799, h3815, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                              · linarith only [h3815, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h3798, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h3797, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h3746, h3796, hlam]
                                  · linarith only [h2678, h3745, h3795, hlam]
                                · linarith only [h0, h3794, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3742, h3793, hlam]
                            · linarith only [h0, h3741, h3792, hlam]
                          · linarith only [h3748, h3791, hc04, hlam, hphi, ht45, ht56, u6elo5]
                        · linarith only [h3742, h3790, hc24, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h3747, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · linarith only [h2678, h3739, h3746, hlam]
                · linarith only [h2678, h3738, h3745, hlam]
              · linarith only [h2678, h3738, h3741, h3744, hc14, hlam, hphi, ht45, ht56, u6elo2]
            · linarith only [h2678, h3739, h3741, h3743, hlam]
          · linarith only [h2678, h3738, h3741, h3742, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3833 | h3833
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3834 | h3834
            · rcases m.htr 0 2 6 (by decide) (by decide) with h3835 | h3835
              · rcases m.htr 0 3 4 (by decide) (by decide) with h3836 | h3836
                · rcases m.htr 0 3 5 (by decide) (by decide) with h3837 | h3837
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h3838 | h3838
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h3839 | h3839
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h3840 | h3840
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h3841 | h3841
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h3842 | h3842
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h3843 | h3843
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h3844 | h3844
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h3845 | h3845
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3846 | h3846
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h3847 | h3847
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h3848 | h3848
                                        · linarith only [h0, h3739, h3741, h3842, h3848, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h3848, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h3741, h3842, h3847, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h3741, h3837, h3842, h3846, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h3741, h3836, h3842, h3845, hlam]
                                · linarith only [h3844, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3833, h3843, hlam]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h3856 | h3856
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h3857 | h3857
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h3858 | h3858
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3859 | h3859
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h3860 | h3860
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h3861 | h3861
                                        · linarith only [h0, h3739, h3842, h3861, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h3861, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h3842, h3860, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h3837, h3859, hlam]
                                  · linarith only [h2678, h3836, h3858, hlam]
                                · linarith only [h0, h3738, h3856, h3857, hc24, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h0, h3833, h3856, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h3841, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h3839, h3840, hc45, hlam, hphi, ht56, u6elo4]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h3871 | h3871
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h3872 | h3872
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h3873 | h3873
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h3874 | h3874
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h3875 | h3875
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h3876 | h3876
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3877 | h3877
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h3878 | h3878
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h3879 | h3879
                                        · linarith only [h0, h3739, h3741, h3873, h3879, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h3879, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h3741, h3873, h3878, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h3741, h3837, h3873, h3877, hlam]
                                  · linarith only [h3741, h3836, h3873, h3876, hlam]
                                · linarith only [h3875, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3833, h3874, hlam]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h3887 | h3887
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h3888 | h3888
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h3889 | h3889
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3890 | h3890
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h3891 | h3891
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h3892 | h3892
                                        · linarith only [h0, h3739, h3873, h3892, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h3892, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h3741, h3891, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h3738, h3837, h3873, h3887, h3890, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h2678, h3836, h3889, hlam]
                                · linarith only [h0, h3738, h3887, h3888, hc24, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h0, h3833, h3887, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h3839, h3872, hc04, hlam, hphi, ht45, ht56, u6elo5]
                        · linarith only [h3833, h3871, hc24, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h3741, h3838, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                  · linarith only [h0, h3739, h3741, h3837, hlam]
                · linarith only [h0, h3738, h3741, h3836, hlam]
              · linarith only [h0, h3738, h3835, hc14, hlam, hphi, ht45, ht56, u6elo2]
            · linarith only [h0, h3739, h3834, hlam]
          · linarith only [h0, h3738, h3833, hlam]
      · linarith only [h3738, h3740, hc14, hlam, hphi, ht45, ht56, u6elo1]
    · rcases m.htr 0 1 6 (by decide) (by decide) with h3909 | h3909
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3910 | h3910
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3911 | h3911
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3912 | h3912
            · rcases m.htr 0 2 6 (by decide) (by decide) with h3913 | h3913
              · rcases m.htr 0 3 4 (by decide) (by decide) with h3914 | h3914
                · rcases m.htr 0 3 5 (by decide) (by decide) with h3915 | h3915
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h3916 | h3916
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h3917 | h3917
                      · linarith only [h3738, h3739, h3917, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h3919 | h3919
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h3920 | h3920
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h3921 | h3921
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h3922 | h3922
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h3923 | h3923
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h3924 | h3924
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3925 | h3925
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h3926 | h3926
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h3927 | h3927
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3928 | h3928
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3929 | h3929
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h3930 | h3930
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3931 | h3931
                                                · linarith only [h3738, h3917, h3922, h3931, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h3933 | h3933
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3934 | h3934
                                                    · linarith only [h3910, h3917, h3928, h3934, hc05, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h3936 | h3936
                                                      · linarith only [h3910, h3929, h3934, h3936, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                      · linarith only [h3936, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h3933, hc25, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h3930, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h3910, h3915, h3928, h3929, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3942 | h3942
                                            · linarith only [h3910, h3914, h3928, h3942, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h3944 | h3944
                                              · linarith only [h3738, h3739, h3921, h3924, h3925, h3928, h3944, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h3944, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h3738, h3739, h3927, hc14, hc56, hlam, hphi, ht45]
                                      · linarith only [h3926, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h3915, h3925, hlam]
                                  · linarith only [h2678, h3914, h3924, hlam]
                                · linarith only [h3923, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3911, h3922, hlam]
                            · linarith only [h0, h3910, h3921, hlam]
                          · linarith only [h3920, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h3919, hc04, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h3916, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h3957 | h3957
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h3958 | h3958
                      · linarith only [h2678, h3738, h3915, h3958, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h3960 | h3960
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h3961 | h3961
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h3962 | h3962
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h3963 | h3963
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h3964 | h3964
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h3965 | h3965
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3966 | h3966
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h3967 | h3967
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h3968 | h3968
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3969 | h3969
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3970 | h3970
                                            · linarith only [h3910, h3915, h3970, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h3972 | h3972
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3973 | h3973
                                                · linarith only [h2678, h3738, h3915, h3958, h3962, h3963, h3966, h3973, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h3975 | h3975
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3976 | h3976
                                                    · linarith only [h2678, h3738, h3915, h3958, h3960, h3962, h3963, h3966, h3969, h3976, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h3978 | h3978
                                                      · linarith only [h2678, h3738, h3915, h3962, h3963, h3966, h3969, h3978, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                      · linarith only [h3978, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h3970, h3975, hc23, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                              · linarith only [h3969, h3972, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                          · linarith only [h3914, h3915, h3962, h3966, h3969, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h3968, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h3915, h3966, h3967, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h3986 | h3986
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h3987 | h3987
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3988 | h3988
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3989 | h3989
                                            · linarith only [h2678, h3966, h3989, hc01, hc23, hlam, hphi, ht12]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h3991 | h3991
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3992 | h3992
                                                · linarith only [h2678, h3738, h3958, h3963, h3966, h3992, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h3994 | h3994
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3995 | h3995
                                                    · linarith only [h2678, h3738, h3958, h3963, h3966, h3988, h3995, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                                    · linarith only [h2678, h3738, h3966, h3995, hc14, hc45, hlam, hphi]
                                                  · linarith only [h3989, h3994, hc23, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                              · linarith only [h3988, h3991, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                          · linarith only [h2678, h3914, h3966, h3988, hc23, hc35, hlam, hphi]
                                        · linarith only [h2678, h3738, h3966, h3987, hc14, hc56, hlam, hphi, ht45]
                                      · linarith only [h2678, h3738, h3963, h3986, hc24, hlam, hphi, ht45, ht56, u6elo3]
                                  · linarith only [h2678, h3914, h3965, hlam]
                                · linarith only [h3964, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3911, h3963, hlam]
                            · linarith only [h0, h3910, h3962, hlam]
                          · linarith only [h3915, h3961, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                        · linarith only [h3960, hc04, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h2678, h3957, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                · linarith only [h2678, h3738, h3914, hlam]
              · linarith only [h3913, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h4012 | h4012
              · rcases m.htr 0 3 4 (by decide) (by decide) with h4013 | h4013
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4014 | h4014
                  · linarith only [h3910, h3912, h4014, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4016 | h4016
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4017 | h4017
                      · linarith only [h2678, h3738, h3910, h3912, h4017, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4019 | h4019
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4020 | h4020
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4021 | h4021
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4022 | h4022
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4023 | h4023
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4024 | h4024
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4025 | h4025
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4026 | h4026
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4027 | h4027
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4028 | h4028
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4029 | h4029
                                            · linarith only [h2678, h3738, h3910, h4014, h4022, h4028, h4029, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                            · linarith only [h3910, h3912, h4021, h4025, h4028, h4029, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                          · linarith only [h4013, h4014, h4021, h4025, h4028, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h4027, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h4014, h4025, h4026, hc03, hc36, hlam, hphi]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4035 | h4035
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4036 | h4036
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4037 | h4037
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4038 | h4038
                                            · linarith only [h2678, h4025, h4038, hc01, hc23, hlam, hphi, ht12]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4040 | h4040
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4041 | h4041
                                                · linarith only [h3738, h3739, h4017, h4022, h4041, hlam]
                                                · linarith only [h3910, h3912, h4037, h4041, hc34, hc45, hlam, hphi]
                                              · linarith only [h4037, h4040, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                          · linarith only [h2678, h4013, h4025, h4037, hc23, hc35, hlam, hphi]
                                        · linarith only [h4036, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4035, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h2678, h3738, h3910, h4013, h4022, h4024, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                · linarith only [h4023, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h2678, h3911, h4021, h4022, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h0, h3738, h3910, h4021, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                          · linarith only [h4020, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4019, hc04, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h4016, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h2678, h3738, h4013, hlam]
              · linarith only [h4012, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
          · linarith only [h2678, h3738, h3910, h3911, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4058 | h4058
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4059 | h4059
            · rcases m.htr 0 2 6 (by decide) (by decide) with h4060 | h4060
              · rcases m.htr 0 3 4 (by decide) (by decide) with h4061 | h4061
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4062 | h4062
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4063 | h4063
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4064 | h4064
                      · linarith only [h3738, h3739, h4064, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4066 | h4066
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4067 | h4067
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4068 | h4068
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4069 | h4069
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4070 | h4070
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4071 | h4071
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4072 | h4072
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4073 | h4073
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4074 | h4074
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4075 | h4075
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4076 | h4076
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4077 | h4077
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4078 | h4078
                                                · linarith only [h3738, h4064, h4069, h4078, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4080 | h4080
                                                  · linarith only [h3910, h4059, h4068, h4080, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                                  · linarith only [h4080, hc25, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h3739, h3910, h4059, h4077, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h3910, h4062, h4076, hlam]
                                          · linarith only [h3910, h4061, h4075, hlam]
                                        · linarith only [h3738, h3739, h4074, hc14, hc56, hlam, hphi, ht45]
                                      · linarith only [h3739, h3910, h4059, h4068, h4073, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h3910, h4059, h4062, h4068, h4072, hlam]
                                  · linarith only [h3910, h4061, h4068, h4071, hlam]
                                · linarith only [h3738, h3739, h3910, h4059, h4068, h4069, h4070, hc24, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                              · linarith only [h3738, h3739, h3910, h4059, h4068, h4069, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4092 | h4092
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4093 | h4093
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4094 | h4094
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4095 | h4095
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4096 | h4096
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4097 | h4097
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4098 | h4098
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4099 | h4099
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4100 | h4100
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4101 | h4101
                                                · linarith only [h3738, h4064, h4066, h4092, h4101, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4103 | h4103
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4104 | h4104
                                                    · linarith only [h3738, h3739, h4061, h4064, h4104, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4106 | h4106
                                                      · linarith only [h0, h3738, h4068, h4092, h4098, h4106, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                      · linarith only [h4064, h4066, h4106, hc34, hc45, hlam, hphi]
                                                  · linarith only [h4103, hc25, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h0, h4068, h4100, hc01, hc36, hlam, hphi, ht12, ht23]
                                            · linarith only [h0, h4068, h4099, hc01, hc35, hlam, hphi, ht12, ht23]
                                          · linarith only [h0, h3738, h4068, h4092, h4098, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                        · linarith only [h3738, h3739, h4092, h4097, hc24, hc56, hlam, hphi, ht45]
                                      · linarith only [h4096, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4062, h4095, hlam]
                                  · linarith only [h2678, h4061, h4094, hlam]
                                · linarith only [h0, h3738, h4092, h4093, hc24, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h0, h4058, h4092, hlam]
                          · linarith only [h4067, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4066, hc04, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h4063, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · linarith only [h3910, h4059, h4062, hlam]
                · linarith only [h0, h3738, h3910, h4061, hlam]
              · linarith only [h3738, h3739, h4059, h4060, hc14, hlam, hphi, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h4125 | h4125
              · rcases m.htr 0 3 4 (by decide) (by decide) with h4126 | h4126
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4127 | h4127
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4128 | h4128
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4129 | h4129
                      · linarith only [h0, h3738, h4059, h4129, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4131 | h4131
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4132 | h4132
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4133 | h4133
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4134 | h4134
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4135 | h4135
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4136 | h4136
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4137 | h4137
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4138 | h4138
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4139 | h4139
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4140 | h4140
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4141 | h4141
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4142 | h4142
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4143 | h4143
                                                · linarith only [h3738, h4129, h4134, h4143, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4145 | h4145
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4146 | h4146
                                                    · linarith only [h0, h3738, h4059, h4134, h4140, h4143, h4146, hlam]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4148 | h4148
                                                      · linarith only [h0, h3738, h4059, h4133, h4134, h4140, h4141, h4148, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                      · linarith only [h4148, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h0, h3738, h4059, h4145, hc14, hc56, hlam, hphi, ht45]
                                              · linarith only [h0, h4059, h4141, h4142, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h0, h3910, h4127, h4141, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                          · linarith only [h3910, h4126, h4140, hlam]
                                        · linarith only [h3738, h3739, h4134, h4139, hc24, hc56, hlam, hphi, ht45]
                                      · linarith only [h3910, h4133, h4138, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h3738, h3910, h4127, h4133, h4134, h4137, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h3910, h4126, h4133, h4136, hlam]
                                · linarith only [h4135, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3910, h4133, h4134, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4161 | h4161
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4162 | h4162
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4163 | h4163
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4164 | h4164
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4165 | h4165
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4166 | h4166
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4167 | h4167
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4168 | h4168
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4169 | h4169
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4170 | h4170
                                                · linarith only [h0, h3738, h4133, h4161, h4170, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4172 | h4172
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4173 | h4173
                                                    · linarith only [h0, h3738, h4133, h4161, h4167, h4170, h4173, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4175 | h4175
                                                      · linarith only [h0, h3738, h4133, h4161, h4167, h4175, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                      · linarith only [h4175, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h0, h3738, h4059, h4172, hc14, hc56, hlam, hphi, ht45]
                                              · linarith only [h0, h4133, h4169, hc01, hc36, hlam, hphi, ht12, ht23]
                                            · linarith only [h0, h4127, h4133, h4168, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo4]
                                          · linarith only [h0, h3738, h4133, h4161, h4167, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                        · linarith only [h3739, h4166, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4165, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h3738, h4127, h4133, h4161, h4164, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h2678, h4126, h4163, hlam]
                                · linarith only [h0, h3738, h4161, h4162, hc24, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h0, h4058, h4161, hlam]
                          · linarith only [h4132, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4131, hc04, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h4128, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4191 | h4191
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4192 | h4192
                      · linarith only [h0, h3738, h3910, h4127, h4192, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4194 | h4194
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4195 | h4195
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4196 | h4196
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4197 | h4197
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4198 | h4198
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4199 | h4199
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4200 | h4200
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4201 | h4201
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4202 | h4202
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4203 | h4203
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4204 | h4204
                                            · linarith only [h0, h3738, h3910, h4127, h4196, h4197, h4203, h4204, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                            · linarith only [h0, h3738, h3910, h4197, h4200, h4203, h4204, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                          · linarith only [h0, h3910, h4126, h4203, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                        · linarith only [h4127, h4200, h4202, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                      · linarith only [h4201, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4210 | h4210
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4211 | h4211
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4212 | h4212
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4213 | h4213
                                            · linarith only [h4196, h4200, h4213, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4215 | h4215
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4216 | h4216
                                                · linarith only [h0, h3738, h3910, h4192, h4196, h4197, h4200, h4216, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4218 | h4218
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4219 | h4219
                                                    · linarith only [h0, h3738, h3910, h4196, h4197, h4200, h4212, h4216, h4219, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                    · linarith only [h0, h3738, h3910, h4196, h4197, h4200, h4212, h4219, hc34, hc45, hlam, hphi]
                                                  · linarith only [h0, h3738, h3910, h4197, h4212, h4213, h4218, hc34, hc56, hlam, hphi, ht45]
                                              · linarith only [h0, h3738, h3910, h4197, h4212, h4215, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                          · linarith only [h0, h3738, h3910, h4126, h4197, h4212, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                        · linarith only [h0, h3738, h3910, h4196, h4197, h4200, h4211, hc24, hc56, hlam, hphi, ht45]
                                      · linarith only [h0, h3738, h3910, h4196, h4197, h4210, hc24, hlam, hphi, ht45, ht56, u6elo3]
                                  · linarith only [h0, h3738, h3910, h4126, h4196, h4197, h4199, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                · linarith only [h4198, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3738, h3910, h4196, h4197, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4230 | h4230
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4231 | h4231
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4232 | h4232
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4233 | h4233
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4234 | h4234
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4235 | h4235
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4236 | h4236
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4237 | h4237
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4238 | h4238
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4239 | h4239
                                                · linarith only [h0, h3738, h4196, h4230, h4239, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4241 | h4241
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4242 | h4242
                                                    · linarith only [h4126, h4127, h4237, h4239, h4242, hlam]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4244 | h4244
                                                      · linarith only [h0, h3738, h3910, h4127, h4230, h4233, h4236, h4244, hc13, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                      · linarith only [h4244, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h0, h3738, h3910, h4127, h4237, h4241, hc14, hc56, hlam, hphi, ht45]
                                              · linarith only [h0, h3738, h3910, h4127, h4196, h4230, h4233, h4236, h4238, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                            · linarith only [h4196, h4233, h4237, hlam]
                                          · linarith only [h0, h3738, h3910, h4127, h4196, h4230, h4233, h4236, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                        · linarith only [h0, h3738, h3910, h4127, h4230, h4233, h4235, hc24, hc56, hlam, hphi, ht45]
                                      · linarith only [h0, h3738, h3910, h4127, h4230, h4233, h4234, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4253 | h4253
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4254 | h4254
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4255 | h4255
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4256 | h4256
                                            · linarith only [h2678, h3738, h4230, h4233, h4255, h4256, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                            · linarith only [h0, h3738, h4196, h4230, h4255, h4256, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                          · linarith only [h0, h3738, h4196, h4230, h4255, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                        · linarith only [h4254, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h3738, h4196, h4230, h4253, hc24, hlam, hphi, ht45, ht56, u6elo3]
                                  · linarith only [h0, h3738, h4126, h4196, h4230, h4232, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                · linarith only [h0, h3738, h4230, h4231, hc24, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h0, h4058, h4230, hlam]
                          · linarith only [h4195, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4194, hc04, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h3910, h4191, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                · linarith only [h0, h3738, h3910, h4126, hlam]
              · linarith only [h0, h3738, h4125, hc14, hlam, hphi, ht45, ht56, u6elo2]
          · linarith only [h0, h3738, h4058, hlam]
      · linarith only [h3738, h3909, hc14, hlam, hphi, ht45, ht56, u6elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4272 | h4272
    · rcases m.htr 0 1 6 (by decide) (by decide) with h4273 | h4273
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4274 | h4274
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4275 | h4275
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4276 | h4276
            · rcases m.htr 0 2 6 (by decide) (by decide) with h4277 | h4277
              · rcases m.htr 0 3 4 (by decide) (by decide) with h4278 | h4278
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4279 | h4279
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4280 | h4280
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4281 | h4281
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4282 | h4282
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4283 | h4283
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4284 | h4284
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4285 | h4285
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4286 | h4286
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4287 | h4287
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4288 | h4288
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4289 | h4289
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4290 | h4290
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4291 | h4291
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4292 | h4292
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4293 | h4293
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4294 | h4294
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4295 | h4295
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4296 | h4296
                                                    · linarith only [h4274, h4291, h4296, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                                    · linarith only [h4274, h4291, h4294, h4296, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                  · linarith only [h4295, hc25, hlam, hphi, ht56, u6elo5]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4300 | h4300
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4301 | h4301
                                                    · linarith only [h4274, h4278, h4294, h4301, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4303 | h4303
                                                      · linarith only [h4274, h4278, h4281, h4291, h4294, h4303, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                      · linarith only [h4303, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h4300, hc25, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h4293, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h4274, h4279, h4291, h4292, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4309 | h4309
                                            · linarith only [h4274, h4278, h4291, h4309, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4311 | h4311
                                              · linarith only [h3738, h4272, h4274, h4278, h4288, h4309, h4311, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                              · linarith only [h4311, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4290, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h3738, h4287, h4289, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4279, h4288, hlam]
                                  · linarith only [h2678, h4278, h4287, hlam]
                                · linarith only [h0, h4286, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4275, h4285, hlam]
                            · linarith only [h0, h4274, h4284, hlam]
                          · linarith only [h4283, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4282, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h3738, h4272, h4281, hlam]
                    · linarith only [h3738, h4272, h4278, h4280, hc15, hlam, hphi, ht56, u6elo3]
                  · linarith only [h3738, h4272, h4278, h4279, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4326 | h4326
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4327 | h4327
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4328 | h4328
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4329 | h4329
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4330 | h4330
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4331 | h4331
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4332 | h4332
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4333 | h4333
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4334 | h4334
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4335 | h4335
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4336 | h4336
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4337 | h4337
                                        · linarith only [h2678, h4272, h4278, h4331, h4334, h4337, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h4337, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4278, h4334, h4336, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · linarith only [h2678, h4278, h4334, h4335, hc01, hc35, hlam, hphi, ht12, ht23]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4342 | h4342
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4343 | h4343
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4344 | h4344
                                        · linarith only [h2678, h4272, h4334, h4344, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4344, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4343, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4272, h4326, h4330, h4342, hc56, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h4333, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4275, h4332, hlam]
                            · linarith only [h0, h4274, h4331, hlam]
                          · linarith only [h4330, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4329, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h2678, h4272, h4278, h4328, hlam]
                    · linarith only [h2678, h4327, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                  · linarith only [h2678, h4272, h4326, hlam]
              · linarith only [h4277, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · linarith only [h0, h4272, h4276, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4359 | h4359
            · rcases m.htr 0 2 6 (by decide) (by decide) with h4360 | h4360
              · rcases m.htr 0 3 4 (by decide) (by decide) with h4361 | h4361
                · linarith only [h4274, h4275, h4361, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4363 | h4363
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4364 | h4364
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4365 | h4365
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4366 | h4366
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4367 | h4367
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4368 | h4368
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4369 | h4369
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4370 | h4370
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4371 | h4371
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4372 | h4372
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4373 | h4373
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4374 | h4374
                                        · linarith only [h2678, h4272, h4274, h4275, h4369, h4374, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h4374, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4361, h4371, h4373, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · linarith only [h2678, h4361, h4371, h4372, hc01, hc35, hlam, hphi, ht12, ht23]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4379 | h4379
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4380 | h4380
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4381 | h4381
                                        · linarith only [h0, h4272, h4275, h4369, h4381, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h4381, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4380, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4272, h4363, h4367, h4379, hc56, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h4275, h4369, h4370, hc02, hc26, hlam, hphi]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4387 | h4387
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4388 | h4388
                                  · linarith only [h2678, h4272, h4361, h4367, h4368, h4369, h4388, hc24, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4390 | h4390
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4391 | h4391
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4392 | h4392
                                        · linarith only [h0, h4272, h4369, h4392, hc24, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h4390, h4392, hc35, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4391, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4274, h4363, h4390, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                                · linarith only [h2678, h4272, h4368, h4387, hc15, hlam, hphi, ht56, u6elo2]
                            · linarith only [h0, h4274, h4368, hlam]
                          · linarith only [h4367, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4366, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h0, h4272, h4275, h4365, hlam]
                    · linarith only [h2678, h4364, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                  · linarith only [h2678, h4272, h4363, hlam]
              · linarith only [h2678, h4272, h4274, h4360, hc15, hlam, hphi, ht56, u6elo2]
            · linarith only [h2678, h4272, h4274, h4359, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4406 | h4406
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4407 | h4407
            · rcases m.htr 0 2 6 (by decide) (by decide) with h4408 | h4408
              · rcases m.htr 0 3 4 (by decide) (by decide) with h4409 | h4409
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4410 | h4410
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4411 | h4411
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4412 | h4412
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4413 | h4413
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4414 | h4414
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4415 | h4415
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4416 | h4416
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4417 | h4417
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4418 | h4418
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4419 | h4419
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4420 | h4420
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4421 | h4421
                                        · linarith only [h3738, h4272, h4274, h4406, h4415, h4421, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h4421, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h3738, h4274, h4406, h4415, h4420, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h3738, h4274, h4406, h4410, h4415, h4419, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h2678, h4272, h4406, h4409, h4418, hc15, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                · linarith only [h4274, h4415, h4417, hc02, hc26, hlam, hphi]
                              · linarith only [h4274, h4406, h4415, h4416, hlam]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4429 | h4429
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4430 | h4430
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4431 | h4431
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4432 | h4432
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4433 | h4433
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4434 | h4434
                                        · linarith only [h0, h4272, h4415, h4434, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h4434, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h3738, h4415, h4429, h4433, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h3738, h4410, h4415, h4429, h4432, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h2678, h4272, h4406, h4409, h4414, h4431, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h0, h4430, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4272, h4406, h4414, h4429, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                          · linarith only [h4414, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h3738, h4272, h4413, hc15, hlam, hphi, ht56, u6elo4]
                      · linarith only [h3738, h4272, h4412, hlam]
                    · linarith only [h4411, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · linarith only [h0, h4272, h4274, h4410, hlam]
                · linarith only [h4274, h4406, h4409, hlam]
              · linarith only [h3738, h4272, h4406, h4408, hc15, hlam, hphi, ht56, u6elo2]
            · linarith only [h3738, h4272, h4406, h4407, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4450 | h4450
            · rcases m.htr 0 2 6 (by decide) (by decide) with h4451 | h4451
              · rcases m.htr 0 3 4 (by decide) (by decide) with h4452 | h4452
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4453 | h4453
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4454 | h4454
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4455 | h4455
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4456 | h4456
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4457 | h4457
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4458 | h4458
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4459 | h4459
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4460 | h4460
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4461 | h4461
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4462 | h4462
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4463 | h4463
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4464 | h4464
                                        · linarith only [h0, h4272, h4274, h4458, h4464, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h4464, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4406, h4459, h4461, h4463, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4406, h4453, h4459, h4461, h4462, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h2678, h4272, h4452, h4461, hc15, hlam, hphi, ht0b, ht56, ht6b, u0elo3]
                                · linarith only [h4274, h4458, h4460, hc03, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4272, h4274, h4458, h4459, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4472 | h4472
                              · linarith only [h0, h4272, h4406, h4458, h4472, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4474 | h4474
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4475 | h4475
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4476 | h4476
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4477 | h4477
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4478 | h4478
                                        · linarith only [h0, h4272, h4458, h4478, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h4478, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4472, h4475, h4477, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4453, h4472, h4475, h4476, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h2678, h4452, h4475, hlam]
                                · linarith only [h0, h4272, h4474, hc15, hlam, hphi, ht56, u6elo2]
                          · linarith only [h4457, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h0, h4272, h4406, h4456, hc15, hlam, hphi, ht56, u6elo4]
                      · linarith only [h0, h4272, h4406, h4455, hlam]
                    · linarith only [h4454, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · linarith only [h0, h4272, h4406, h4452, h4453, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4490 | h4490
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4491 | h4491
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4492 | h4492
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4493 | h4493
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4494 | h4494
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4495 | h4495
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4496 | h4496
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4497 | h4497
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4498 | h4498
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4499 | h4499
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4500 | h4500
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4501 | h4501
                                        · linarith only [h2678, h4272, h4452, h4498, h4501, hc13, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h4499, h4501, hc35, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4274, h4452, h4498, h4500, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · linarith only [h0, h4274, h4452, h4498, h4499, hc01, hc35, hlam, hphi, ht12, ht23]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4506 | h4506
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4507 | h4507
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4508 | h4508
                                        · linarith only [h0, h4272, h4274, h4495, h4498, h4508, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4506, h4508, hc35, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4274, h4495, h4507, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4274, h4490, h4495, h4506, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                · linarith only [h0, h4272, h4406, h4496, h4497, hc15, hc26, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                              · linarith only [h0, h4272, h4274, h4495, h4496, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4515 | h4515
                              · linarith only [h0, h4272, h4406, h4495, h4515, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4517 | h4517
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4518 | h4518
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4519 | h4519
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4520 | h4520
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4521 | h4521
                                        · linarith only [h0, h4272, h4495, h4521, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h4519, h4521, hc35, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4274, h4452, h4518, h4520, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · linarith only [h0, h4274, h4452, h4518, h4519, hc01, hc35, hlam, hphi, ht12, ht23]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4526 | h4526
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4527 | h4527
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4528 | h4528
                                        · linarith only [h0, h4272, h4495, h4528, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h4526, h4528, hc35, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4495, h4527, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4490, h4495, h4526, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                · linarith only [h0, h4272, h4517, hc15, hlam, hphi, ht56, u6elo2]
                          · linarith only [h4494, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4493, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h2678, h4272, h4452, h4492, hlam]
                    · linarith only [h0, h4274, h4491, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                  · linarith only [h0, h4272, h4274, h4490, hlam]
              · linarith only [h0, h4272, h4451, hc15, hlam, hphi, ht56, u6elo2]
            · linarith only [h0, h4272, h4450, hlam]
      · linarith only [h4272, h4273, hc15, hlam, hphi, ht56, u6elo1]
    · rcases m.htr 0 1 6 (by decide) (by decide) with h4542 | h4542
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4543 | h4543
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4544 | h4544
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4545 | h4545
            · rcases m.htr 0 2 6 (by decide) (by decide) with h4546 | h4546
              · rcases m.htr 0 3 4 (by decide) (by decide) with h4547 | h4547
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4548 | h4548
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4549 | h4549
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4550 | h4550
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4551 | h4551
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4552 | h4552
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4553 | h4553
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4554 | h4554
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4555 | h4555
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4556 | h4556
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4557 | h4557
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4558 | h4558
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4559 | h4559
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4560 | h4560
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4561 | h4561
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4562 | h4562
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4563 | h4563
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4564 | h4564
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4565 | h4565
                                                    · linarith only [h4543, h4560, h4565, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                                    · linarith only [h4543, h4560, h4563, h4565, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                  · linarith only [h4564, hc25, hlam, hphi, ht56, u6elo5]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4569 | h4569
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4570 | h4570
                                                    · linarith only [h4543, h4547, h4563, h4570, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4572 | h4572
                                                      · linarith only [h4543, h4547, h4550, h4560, h4563, h4572, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                      · linarith only [h4572, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h4569, hc25, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h4562, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h4543, h4548, h4560, h4561, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4578 | h4578
                                            · linarith only [h4543, h4547, h4560, h4578, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4580 | h4580
                                              · linarith only [h4543, h4547, h4560, h4580, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                              · linarith only [h4580, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4272, h4559, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                                      · linarith only [h2678, h4558, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h3738, h4542, h4548, h4555, h4556, h4557, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h2678, h4547, h4556, hlam]
                                · linarith only [h0, h4555, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4544, h4554, hlam]
                            · linarith only [h0, h4543, h4553, hlam]
                          · linarith only [h4272, h4552, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                        · linarith only [h4272, h4542, h4550, h4551, hc16, hlam, hphi, u6elo4]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4592 | h4592
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4593 | h4593
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4594 | h4594
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4595 | h4595
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4596 | h4596
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4597 | h4597
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4598 | h4598
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4599 | h4599
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4600 | h4600
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4601 | h4601
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4602 | h4602
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4603 | h4603
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4604 | h4604
                                                · linarith only [h4544, h4550, h4604, hlam]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4606 | h4606
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4607 | h4607
                                                    · linarith only [h3738, h4542, h4543, h4550, h4596, h4601, h4603, h4607, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4609 | h4609
                                                      · linarith only [h4543, h4602, h4607, h4609, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                      · linarith only [h4609, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h4604, h4606, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                              · linarith only [h4602, h4603, hc35, hlam, hphi, ht56, u6elo3]
                                            · linarith only [h4548, h4601, h4602, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4615 | h4615
                                            · linarith only [h4547, h4601, h4615, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4617 | h4617
                                              · linarith only [h4543, h4547, h4601, h4617, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                              · linarith only [h4617, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4272, h4600, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                                      · linarith only [h3738, h4542, h4596, h4597, h4599, hc26, hlam, hphi, u6elo3]
                                    · linarith only [h2678, h4548, h4598, hlam]
                                  · linarith only [h2678, h4547, h4597, hlam]
                                · linarith only [h2678, h4594, h4596, hc03, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h2678, h4542, h4544, h4594, h4595, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
                            · linarith only [h0, h4543, h4594, hlam]
                          · linarith only [h3738, h4542, h4550, h4593, hc16, hlam, hphi, u6elo5]
                        · linarith only [h3738, h4542, h4592, hc16, hlam, hphi, u6elo4]
                    · linarith only [h4549, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4630 | h4630
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4631 | h4631
                      · linarith only [h4547, h4548, h4631, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4633 | h4633
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4634 | h4634
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4635 | h4635
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4636 | h4636
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4637 | h4637
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4638 | h4638
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4639 | h4639
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4640 | h4640
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4641 | h4641
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4642 | h4642
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4643 | h4643
                                            · linarith only [h4543, h4548, h4643, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4645 | h4645
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4646 | h4646
                                                · linarith only [h4544, h4631, h4646, hlam]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4648 | h4648
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4649 | h4649
                                                    · linarith only [h3738, h4542, h4543, h4631, h4637, h4642, h4645, h4649, hc36, hlam, hphi, ht0b, ht6b, u0elo2]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4651 | h4651
                                                      · linarith only [h4543, h4548, h4635, h4639, h4642, h4651, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                      · linarith only [h4651, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h4643, h4648, hc23, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                              · linarith only [h4642, h4645, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                          · linarith only [h4547, h4548, h4635, h4639, h4642, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h4547, h4548, h4639, h4641, hc34, hc56, hlam, hphi, ht45]
                                      · linarith only [h3738, h4547, h4548, h4639, h4640, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4659 | h4659
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4660 | h4660
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4661 | h4661
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4662 | h4662
                                            · linarith only [h3738, h4542, h4543, h4637, h4638, h4639, h4662, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4664 | h4664
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4665 | h4665
                                                · linarith only [h3738, h4542, h4544, h4631, h4637, h4664, h4665, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4667 | h4667
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4668 | h4668
                                                    · linarith only [h4545, h4631, h4661, h4662, h4668, hc05, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4670 | h4670
                                                      · linarith only [h4545, h4661, h4662, h4670, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                      · linarith only [h4670, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h4662, h4667, hc23, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                              · linarith only [h4661, h4664, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                          · linarith only [h2678, h4547, h4639, h4661, hc23, hc35, hlam, hphi]
                                        · linarith only [h3738, h4638, h4639, h4660, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                                      · linarith only [h3738, h4542, h4637, h4638, h4659, hc26, hlam, hphi, u6elo3]
                                  · linarith only [h2678, h4547, h4638, hlam]
                                · linarith only [h4637, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4544, h4636, hlam]
                            · linarith only [h0, h4543, h4635, hlam]
                          · linarith only [h4548, h4634, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                        · linarith only [h3738, h4633, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo4]
                    · linarith only [h3738, h4542, h4547, h4630, hc16, hlam, hphi, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4685 | h4685
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4686 | h4686
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4687 | h4687
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4688 | h4688
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4689 | h4689
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4690 | h4690
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4691 | h4691
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4692 | h4692
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4693 | h4693
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4694 | h4694
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4695 | h4695
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4696 | h4696
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4697 | h4697
                                          · linarith only [h4272, h4542, h4543, h4547, h4685, h4692, h4697, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4699 | h4699
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4700 | h4700
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4701 | h4701
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4702 | h4702
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4703 | h4703
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4704 | h4704
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h4705 | h4705
                                                        · linarith only [h4543, h4547, h4690, h4693, h4699, h4705, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                                        · linarith only [h4705, hc35, hlam, hphi, ht56, u6elo5]
                                                      · linarith only [h4272, h4542, h4547, h4685, h4692, h4700, h4704, hc36, hlam, hphi, u6elo4]
                                                    · linarith only [h4272, h4542, h4547, h4685, h4687, h4692, h4700, h4703, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                                  · linarith only [h4702, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h4547, h4685, h4687, h4690, h4693, h4697, h4699, h4701, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                              · linarith only [h4699, h4700, hc35, hlam, hphi, ht56, u6elo3]
                                            · linarith only [h4547, h4685, h4690, h4693, h4699, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h4696, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h4272, h4547, h4685, h4693, h4695, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · linarith only [h4547, h4685, h4693, h4694, hlam]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4717 | h4717
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4718 | h4718
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4719 | h4719
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4720 | h4720
                                          · linarith only [h2678, h4542, h4692, h4693, h4720, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4722 | h4722
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4723 | h4723
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4724 | h4724
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4725 | h4725
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4726 | h4726
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4727 | h4727
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h4728 | h4728
                                                        · linarith only [h4543, h4722, h4728, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                                                        · linarith only [h4728, hc35, hlam, hphi, ht56, u6elo5]
                                                      · linarith only [h4272, h4693, h4717, h4727, hc01, hc46, hlam, hphi, ht12, ht23, ht34]
                                                    · linarith only [h4272, h4542, h4692, h4693, h4717, h4723, h4726, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                  · linarith only [h4725, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h4544, h4687, h4720, h4722, h4724, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                              · linarith only [h4722, h4723, hc35, hlam, hphi, ht56, u6elo3]
                                            · linarith only [h2678, h4685, h4693, h4722, hc23, hc34, hlam, hphi]
                                        · linarith only [h4272, h4719, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                                      · linarith only [h2678, h4718, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4542, h4685, h4692, h4717, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h0, h4692, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4544, h4691, hlam]
                            · linarith only [h0, h4543, h4690, hlam]
                          · linarith only [h4272, h4689, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                        · linarith only [h4547, h4688, hc03, hlam, hphi, ht34, ht45, ht56, u6elo4]
                      · linarith only [h4547, h4685, h4687, hlam]
                    · linarith only [h4272, h4542, h4685, h4686, hc16, hlam, hphi, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4747 | h4747
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4748 | h4748
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4749 | h4749
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4750 | h4750
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4751 | h4751
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4752 | h4752
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4753 | h4753
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4754 | h4754
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4755 | h4755
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4756 | h4756
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4757 | h4757
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4758 | h4758
                                          · linarith only [h4543, h4547, h4758, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4760 | h4760
                                            · linarith only [h4543, h4685, h4760, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4762 | h4762
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4763 | h4763
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4764 | h4764
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4765 | h4765
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4766 | h4766
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h4767 | h4767
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h4768 | h4768
                                                          · linarith only [h4544, h4763, h4768, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                                                          · linarith only [h4768, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h2678, h4542, h4685, h4753, h4764, h4767, hlam]
                                                      · linarith only [h2678, h4685, h4765, h4766, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo4]
                                                    · linarith only [h2678, h4542, h4544, h4547, h4748, h4753, h4762, h4765, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                  · linarith only [h4760, h4764, hc23, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                                · linarith only [h4547, h4748, h4751, h4754, h4758, h4762, h4763, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h4762, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4755, h4757, hc35, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4547, h4754, h4756, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · linarith only [h2678, h4547, h4754, h4755, hc01, hc35, hlam, hphi, ht12, ht23]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4780 | h4780
                                    · linarith only [h2678, h4542, h4685, h4753, h4754, h4780, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4782 | h4782
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4783 | h4783
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4784 | h4784
                                          · linarith only [h4543, h4547, h4784, hlam]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4786 | h4786
                                            · linarith only [h4272, h4542, h4543, h4753, h4780, h4786, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4788 | h4788
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4789 | h4789
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4790 | h4790
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4791 | h4791
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4792 | h4792
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h4793 | h4793
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h4794 | h4794
                                                          · linarith only [h4544, h4789, h4794, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                                                          · linarith only [h4794, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h4542, h4753, h4780, h4790, h4793, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                                      · linarith only [h2678, h4542, h4753, h4780, h4788, h4791, h4792, hc36, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h3738, h4748, h4754, h4791, hlam]
                                                  · linarith only [h4790, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h4544, h4748, h4784, h4788, h4789, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                              · linarith only [h4788, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4272, h4783, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4782, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                · linarith only [h4753, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4544, h4752, hlam]
                            · linarith only [h0, h4543, h4751, hlam]
                          · linarith only [h4750, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4749, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4810 | h4810
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4811 | h4811
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4812 | h4812
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4813 | h4813
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4814 | h4814
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4815 | h4815
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4816 | h4816
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4817 | h4817
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4818 | h4818
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4819 | h4819
                                          · linarith only [h4543, h4547, h4819, hlam]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4821 | h4821
                                            · linarith only [h4543, h4685, h4821, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4823 | h4823
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4824 | h4824
                                                · linarith only [h4544, h4748, h4824, hlam]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4826 | h4826
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4827 | h4827
                                                    · linarith only [h4748, h4810, h4812, h4815, h4827, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4829 | h4829
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h4830 | h4830
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h4831 | h4831
                                                          · rcases h0bigk with h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h0, hlam, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h2678, hlam, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h3738, hlam, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4272, hlam, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h2678, h4542, h4547, h4812, h4814, h4815, h4823, h4829, h4831, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4542, h4814, h4823, h4829, h4831, hc56, hlam, hphi, ht0b, ht6b, p4832_1, u0elo1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h2678, h4542, h4814, h4823, h4829, h4831, hc56, hlam, hphi, ht0b, ht6b, p4832_1, u0elo1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h2678, h4542, h4547, h4814, h4823, h4829, h4831, hc56, hlam, hphi, ht0b, ht6b, p4832_1, u0elo1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h2678, h4542, h4547, h4748, h4814, h4823, h4829, h4831, hc56, hlam, hphi, ht0b, ht6b, p4832_1, u0elo1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              rcases p4832_3 (m.d 0 1) (by simp) with h4844 | h4844
                                                              · linarith only [h0, h4844, hlam]
                                                              · linarith only [h4542, h4844, hlam]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4542, h4814, h4823, h4829, h4831, hc56, hlam, hphi, ht0b, ht6b, p4832_1, u0elo2]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4543, hlam, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4547, hlam, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4685, hlam, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4542, h4547, h4812, h4814, h4815, h4823, h4829, h4831, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4542, h4748, h4814, h4823, h4829, h4831, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4544, hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4748, hc03, hc45, hlam, hphi, ht34, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4748, hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              rcases p4832_3 (m.d 0 1) (by simp) with h4858 | h4858
                                                              · linarith only [h3738, h4858, hlam]
                                                              · linarith only [h4542, h4858, hlam]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4542, h4685, h4812, h4814, h4816, h4823, h4829, h4831, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4545, hlam, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h2678, h4542, h4685, h4812, h4814, h4816, h4823, h4829, h4831, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h3738, h4542, h4685, h4812, h4814, h4816, h4823, h4829, h4831, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p4832_1]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              rcases p4832_3 (m.d 0 1) (by simp) with h4866 | h4866
                                                              · linarith only [h4272, h4866, hlam]
                                                              · linarith only [h4542, h4866, hlam]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4542, hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4546, hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4747, hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4810, hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [h4811, hlam, p4832_0]
                                                            · obtain ⟨p4832_0, p4832_1, p4832_2, p4832_3⟩ := h4832c
                                                              linarith only [hlam, p4832_0]
                                                          · linarith only [h4827, h4831, hc34, hlam, hphi, ht45, ht56, u6elo5]
                                                        · linarith only [h2678, h4542, h4547, h4685, h4814, h4826, h4827, h4830, hc05, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b]
                                                      · linarith only [h2678, h4547, h4829, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo4]
                                                  · linarith only [h4824, h4826, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                              · linarith only [h4823, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4818, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4547, h4815, h4817, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · linarith only [h2678, h4542, h4547, h4814, h4815, h4816, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4883 | h4883
                                    · linarith only [h2678, h4542, h4685, h4814, h4815, h4883, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4885 | h4885
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4886 | h4886
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4887 | h4887
                                          · linarith only [h4543, h4547, h4887, hlam]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4889 | h4889
                                            · linarith only [h2678, h4542, h4814, h4883, h4889, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4891 | h4891
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4892 | h4892
                                                · linarith only [h4544, h4748, h4892, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h4894 | h4894
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4895 | h4895
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h4896 | h4896
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h4897 | h4897
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h4898 | h4898
                                                          · rcases h0bigk with h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c | h4899c
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h0, hlam, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h2678, hlam, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h3738, hlam, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4272, hlam, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h2678, h4883, hc06, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4542, h4814, h4891, h4896, h4898, hc56, hlam, hphi, ht0b, ht6b, p4899_1, u0elo1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h2678, h4542, h4814, h4891, h4896, h4898, hc56, hlam, hphi, ht0b, ht6b, p4899_1, u0elo1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h3738, h4542, h4814, h4891, h4896, h4898, hc56, hlam, hphi, ht0b, ht6b, p4899_1, u0elo1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4272, h4542, h4814, h4891, h4896, h4898, hc56, hlam, hphi, ht0b, ht6b, p4899_1, u0elo1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              rcases p4899_3 (m.d 0 1) (by simp) with h4911 | h4911
                                                              · linarith only [h0, h4911, hlam]
                                                              · linarith only [h4542, h4911, hlam]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4542, h4814, h4891, h4896, h4898, hc56, hlam, hphi, ht0b, ht6b, p4899_1, u0elo2]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4543, hlam, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4547, hlam, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4685, hlam, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4542, h4547, h4748, h4814, h4891, h4895, h4896, h4898, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4542, h4748, h4814, h4891, h4895, h4896, h4898, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4544, hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4748, h4895, hc03, hc34, hlam, hphi, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4748, hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4542, h4748, h4814, h4891, h4895, h4896, h4898, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4542, h4748, h4814, h4891, h4895, h4896, h4898, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4545, hlam, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h2678, h4542, h4748, h4814, h4891, h4895, h4896, h4898, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h3738, h4542, h4748, h4814, h4891, h4895, h4896, h4898, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p4899_1]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              rcases p4899_3 (m.d 0 1) (by simp) with h4931 | h4931
                                                              · linarith only [h4272, h4931, hlam]
                                                              · linarith only [h4542, h4931, hlam]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4542, hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4546, hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4747, hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4810, hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [h4811, hlam, p4899_0]
                                                            · obtain ⟨p4899_0, p4899_1, p4899_2, p4899_3⟩ := h4899c
                                                              linarith only [hlam, p4899_0]
                                                          · linarith only [h4748, h4898, hc05, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h2678, h4883, h4897, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45]
                                                      · linarith only [h2678, h4542, h4547, h4748, h4814, h4891, h4895, h4896, hc36, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h2678, h4542, h4814, h4815, h4891, h4895, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                  · linarith only [h4894, hc25, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h4891, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h2678, h4542, h4814, h4883, h4886, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h2678, h4542, h4814, h4885, hc26, hlam, hphi, u6elo3]
                                · linarith only [h0, h4814, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h2678, h4544, h4812, h4813, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h0, h4543, h4812, hlam]
                          · linarith only [h2678, h4542, h4547, h4748, h4811, hc16, hlam, hphi, u6elo5]
                        · linarith only [h2678, h4542, h4547, h4810, hc16, hlam, hphi, u6elo4]
                    · linarith only [h2678, h4542, h4747, hc16, hlam, hphi, u6elo3]
              · linarith only [h4546, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h4955 | h4955
              · rcases m.htr 0 3 4 (by decide) (by decide) with h4956 | h4956
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4957 | h4957
                  · linarith only [h4543, h4545, h4957, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h4959 | h4959
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h4960 | h4960
                      · linarith only [h4543, h4545, h4956, h4960, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h4962 | h4962
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h4963 | h4963
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h4964 | h4964
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h4965 | h4965
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h4966 | h4966
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h4967 | h4967
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4968 | h4968
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4969 | h4969
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4970 | h4970
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4971 | h4971
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4972 | h4972
                                            · linarith only [h3738, h4543, h4956, h4957, h4972, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                                            · linarith only [h4543, h4545, h4964, h4968, h4971, h4972, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                          · linarith only [h4956, h4957, h4964, h4968, h4971, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h4956, h4957, h4968, h4970, hc34, hc56, hlam, hphi, ht45]
                                      · linarith only [h3738, h4956, h4957, h4968, h4969, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h4978 | h4978
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h4979 | h4979
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4980 | h4980
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4981 | h4981
                                            · linarith only [h3738, h4967, h4968, h4981, hc01, hc23, hlam, hphi, ht12]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h4983 | h4983
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4984 | h4984
                                                · linarith only [h4544, h4960, h4984, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                · linarith only [h4543, h4545, h4980, h4984, hc34, hc45, hlam, hphi]
                                              · linarith only [h4980, h4983, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                          · linarith only [h2678, h4956, h4968, h4980, hc23, hc35, hlam, hphi]
                                        · linarith only [h4979, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h3738, h4967, h4978, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h2678, h4956, h4967, hlam]
                                · linarith only [h4966, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4542, h4544, h4965, hc16, hlam, hphi, ht0b, ht6b, u0elo3]
                            · linarith only [h0, h4543, h4964, hlam]
                          · linarith only [h4963, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4962, hc04, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h4956, h4959, hc34, hlam, hphi, ht45, ht56, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h4998 | h4998
                  · linarith only [h4543, h4545, h4998, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5000 | h5000
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5001 | h5001
                      · linarith only [h4544, h4545, h5001, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5003 | h5003
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5004 | h5004
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5005 | h5005
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5006 | h5006
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5007 | h5007
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5008 | h5008
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5009 | h5009
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5010 | h5010
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5011 | h5011
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5012 | h5012
                                          · linarith only [h4543, h4956, h5012, hlam]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5014 | h5014
                                            · linarith only [h4543, h4545, h4998, h5014, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5016 | h5016
                                              · linarith only [h4544, h4545, h5005, h5009, h5012, h5014, h5016, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h5016, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h5011, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h5010, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4542, h4956, h5007, h5008, h5009, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5022 | h5022
                                    · linarith only [h2678, h4542, h4998, h5007, h5008, h5022, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5024 | h5024
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5025 | h5025
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5026 | h5026
                                          · linarith only [h4543, h5008, h5026, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5028 | h5028
                                            · linarith only [h2678, h4542, h4543, h5007, h5022, h5028, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5030 | h5030
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5031 | h5031
                                                · linarith only [h4544, h4545, h5001, h5028, h5031, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5033 | h5033
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5034 | h5034
                                                    · linarith only [h4544, h4545, h5026, h5031, h5034, hc23, hc34, hlam, hphi]
                                                    · linarith only [h2678, h4542, h5007, h5008, h5030, h5034, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                  · linarith only [h4544, h4545, h5026, h5030, h5033, hc36, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b]
                                              · linarith only [h5030, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4272, h5025, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h5024, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                · linarith only [h5007, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h2678, h4542, h4544, h5005, h5006, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
                            · linarith only [h0, h4543, h5005, hlam]
                          · linarith only [h5004, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h2678, h4542, h4956, h5003, hc16, hlam, hphi, u6elo4]
                    · linarith only [h2678, h4542, h5000, hc16, hlam, hphi, u6elo3]
              · linarith only [h4955, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5048 | h5048
            · rcases m.htr 0 2 6 (by decide) (by decide) with h5049 | h5049
              · rcases m.htr 0 3 4 (by decide) (by decide) with h5050 | h5050
                · linarith only [h4543, h4544, h5050, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h5052 | h5052
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5053 | h5053
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5054 | h5054
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5055 | h5055
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5056 | h5056
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5057 | h5057
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5058 | h5058
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5059 | h5059
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5060 | h5060
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5061 | h5061
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5062 | h5062
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5063 | h5063
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5064 | h5064
                                          · linarith only [h4272, h4542, h4543, h5050, h5052, h5059, h5064, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5066 | h5066
                                            · linarith only [h4543, h4544, h5057, h5060, h5064, h5066, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                            · linarith only [h4543, h4544, h5052, h5057, h5060, h5064, h5066, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h4272, h4542, h5059, h5063, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h5062, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h4543, h5050, h5052, h5060, h5061, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5072 | h5072
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5073 | h5073
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5074 | h5074
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5075 | h5075
                                          · linarith only [h4543, h4544, h5058, h5060, h5075, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5077 | h5077
                                            · linarith only [h4543, h4544, h5058, h5077, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                            · linarith only [h4543, h4544, h5052, h5058, h5077, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h4272, h4542, h5059, h5074, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h4272, h4542, h5059, h5072, h5073, hc26, hlam, hphi, u6elo3]
                                    · linarith only [h4543, h4544, h5052, h5058, h5072, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                · linarith only [h4544, h5058, h5059, hc02, hc26, hlam, hphi]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5084 | h5084
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5085 | h5085
                                  · linarith only [h4272, h4542, h5050, h5052, h5057, h5058, h5084, h5085, hc24, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5087 | h5087
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5088 | h5088
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5089 | h5089
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5090 | h5090
                                          · linarith only [h4543, h5085, h5090, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5092 | h5092
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5093 | h5093
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5094 | h5094
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5095 | h5095
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5096 | h5096
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5097 | h5097
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h5098 | h5098
                                                        · linarith only [h4543, h5092, h5098, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                                                        · linarith only [h5098, hc35, hlam, hphi, ht56, u6elo5]
                                                      · linarith only [h0, h4543, h5058, h5090, h5097, hc23, hc46, hlam, hphi, ht34]
                                                    · linarith only [h4272, h4542, h5057, h5058, h5084, h5087, h5090, h5093, h5096, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                  · linarith only [h5095, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h4272, h4542, h5057, h5058, h5084, h5087, h5093, h5094, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                              · linarith only [h5093, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h2678, h5052, h5057, h5058, h5090, h5092, hc23, hc34, hlam, hphi]
                                        · linarith only [h4272, h4542, h5084, h5089, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h4272, h4542, h5084, h5087, h5088, hc26, hlam, hphi, u6elo3]
                                    · linarith only [h2678, h5052, h5087, hlam]
                                · linarith only [h0, h5084, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h0, h4542, h4543, h5057, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
                          · linarith only [h4272, h4542, h5056, hc16, hlam, hphi, u6elo5]
                        · linarith only [h5055, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h4543, h4544, h5052, h5054, hlam]
                    · linarith only [h5053, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5116 | h5116
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5117 | h5117
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5118 | h5118
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5119 | h5119
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5120 | h5120
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5121 | h5121
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5122 | h5122
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5123 | h5123
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5124 | h5124
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5125 | h5125
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5126 | h5126
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5127 | h5127
                                          · linarith only [h2678, h4542, h4543, h4544, h5050, h5121, h5122, h5127, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5129 | h5129
                                            · linarith only [h2678, h4542, h4543, h4544, h5052, h5120, h5122, h5123, h5127, h5129, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5131 | h5131
                                              · linarith only [h4544, h5048, h5120, h5123, h5127, h5129, h5131, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h5131, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h2678, h4542, h5052, h5122, h5124, h5126, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h5125, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4542, h5050, h5122, h5123, h5124, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5137 | h5137
                                    · linarith only [h2678, h4542, h5052, h5122, h5123, h5137, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5139 | h5139
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5140 | h5140
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5141 | h5141
                                          · linarith only [h2678, h4542, h5122, h5123, h5141, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5143 | h5143
                                            · linarith only [h2678, h4542, h4543, h4544, h5121, h5122, h5137, h5143, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5145 | h5145
                                              · linarith only [h4544, h5048, h5121, h5143, h5145, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h5145, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h2678, h4542, h5122, h5137, h5140, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h2678, h4542, h5122, h5139, hc26, hlam, hphi, u6elo3]
                                · linarith only [h4544, h5121, h5122, hc02, hc26, hlam, hphi]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5151 | h5151
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5152 | h5152
                                  · linarith only [h2678, h5050, h5120, h5121, h5152, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5154 | h5154
                                    · linarith only [h2678, h4542, h5052, h5151, h5152, h5154, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5156 | h5156
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5157 | h5157
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5158 | h5158
                                          · linarith only [h4543, h5152, h5158, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5160 | h5160
                                            · linarith only [h2678, h4542, h4543, h5151, h5154, h5160, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5162 | h5162
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5163 | h5163
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5164 | h5164
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5165 | h5165
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5166 | h5166
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h5167 | h5167
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h5168 | h5168
                                                          · rcases h0bigk with h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h0, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h2678, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h3738, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h4272, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h2678, h5154, hc06, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h0, h5121, h5158, hc01, hc34, hlam, hphi, ht12, ht23, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h0, h2678, h4542, h5121, h5151, h5158, h5162, h5166, h5168, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h4544, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h0, h2678, h4542, h5052, h5121, h5151, h5158, h5162, h5166, h5168, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              rcases p5169_3 (m.d 0 1) (by simp) with h5181 | h5181
                                                              · linarith only [h0, h5181, hlam]
                                                              · linarith only [h4542, h5181, hlam]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h4542, h5151, h5162, h5166, h5168, hc56, hlam, hphi, ht0b, ht6b, p5169_1, u0elo2]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h4543, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h5050, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h5052, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              rcases p5169_3 (m.d 0 1) (by simp) with h5189 | h5189
                                                              · linarith only [h2678, h5189, hlam]
                                                              · linarith only [h4542, h5189, hlam]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h4542, h5151, h5162, h5166, h5168, hc56, hlam, hphi, ht0b, ht6b, p5169_1, u0elo3]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h5048, h5160, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p5169_1, u0elo3]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h2678, h4542, h5151, h5162, h5166, h5168, hc56, hlam, hphi, ht0b, ht6b, p5169_1, u0elo3]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h4272, h4542, h5151, h5162, h5166, h5168, hc56, hlam, hphi, ht0b, ht6b, p5169_1, u0elo3]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              rcases p5169_3 (m.d 0 1) (by simp) with h5197 | h5197
                                                              · linarith only [h3738, h5197, hlam]
                                                              · linarith only [h4542, h5197, hlam]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h4542, h5151, h5162, h5166, h5168, hc56, hlam, hphi, ht0b, ht6b, p5169_1, u0elo4]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h5048, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h0, h2678, h4542, h5048, h5121, h5151, h5158, h5162, h5166, h5168, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h5117, hlam, p5169_1]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              rcases p5169_3 (m.d 0 1) (by simp) with h5205 | h5205
                                                              · linarith only [h4272, h5205, hlam]
                                                              · linarith only [h4542, h5205, hlam]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h4542, hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h5049, hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h5116, hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h5118, hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [h5119, hlam, p5169_0]
                                                            · obtain ⟨p5169_0, p5169_1, p5169_2, p5169_3⟩ := h5169c
                                                              linarith only [hlam, p5169_0]
                                                          · linarith only [h5168, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h2678, h4542, h5120, h5121, h5151, h5158, h5164, h5167, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                      · linarith only [h2678, h5120, h5121, h5158, h5166, hc01, hc46, hlam, hphi, ht12, ht23, ht34]
                                                    · linarith only [h2678, h5120, h5121, h5158, h5165, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                                  · linarith only [h5160, h5162, h5164, hc36, hlam, hphi, u6elo5]
                                                · linarith only [h2678, h4542, h5120, h5121, h5151, h5162, h5163, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                              · linarith only [h5162, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4272, h5157, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4542, h5151, h5156, hc26, hlam, hphi, u6elo3]
                                · linarith only [h0, h5151, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h0, h4543, h5120, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h5119, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h5118, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h4544, h5048, h5117, hlam]
                    · linarith only [h5116, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
              · linarith only [h5049, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h5230 | h5230
              · rcases m.htr 0 3 4 (by decide) (by decide) with h5231 | h5231
                · linarith only [h4543, h4544, h5231, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h5233 | h5233
                  · linarith only [h4543, h5048, h5233, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5235 | h5235
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5236 | h5236
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5237 | h5237
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5238 | h5238
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5239 | h5239
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5240 | h5240
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5241 | h5241
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5242 | h5242
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5243 | h5243
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5244 | h5244
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5245 | h5245
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5246 | h5246
                                          · linarith only [h4543, h5231, h5246, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5248 | h5248
                                            · linarith only [h4543, h4544, h5233, h5239, h5242, h5246, h5248, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5250 | h5250
                                              · linarith only [h4543, h4544, h5239, h5242, h5246, h5250, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h5250, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h5245, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h5244, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h4543, h4544, h5231, h5242, h5243, hc23, hc35, hlam, hphi]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5256 | h5256
                                    · linarith only [h2678, h4542, h5233, h5241, h5242, h5256, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5258 | h5258
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5259 | h5259
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5260 | h5260
                                          · linarith only [h4543, h5242, h5260, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5262 | h5262
                                            · linarith only [h2678, h4542, h4543, h4544, h5240, h5241, h5256, h5262, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5264 | h5264
                                              · linarith only [h4543, h4544, h5240, h5264, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h5264, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4272, h5259, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4542, h5241, h5258, hc26, hlam, hphi, u6elo3]
                                · linarith only [h4544, h5240, h5241, hc02, hc26, hlam, hphi]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5270 | h5270
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5271 | h5271
                                  · linarith only [h5231, h5235, h5239, h5240, h5271, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5273 | h5273
                                    · linarith only [h2678, h4542, h5233, h5270, h5271, h5273, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5275 | h5275
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5276 | h5276
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5277 | h5277
                                          · linarith only [h4543, h5271, h5277, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5279 | h5279
                                            · linarith only [h0, h2678, h4542, h4543, h5240, h5270, h5273, h5277, h5279, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5281 | h5281
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5282 | h5282
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5283 | h5283
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5284 | h5284
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5285 | h5285
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h5286 | h5286
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h5287 | h5287
                                                          · rcases h0bigk with h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h0, hlam, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h2678, hlam, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h3738, hlam, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4272, hlam, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h2678, h5273, hc06, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h0, h5240, h5277, hc01, hc34, hlam, hphi, ht12, ht23, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h0, h2678, h4542, h5240, h5270, h5277, h5281, h5285, h5287, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4544, hlam, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h5048, hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              rcases p5288_3 (m.d 0 1) (by simp) with h5300 | h5300
                                                              · linarith only [h0, h5300, hlam]
                                                              · linarith only [h4542, h5300, hlam]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4542, h5270, h5281, h5285, h5287, hc56, hlam, hphi, ht0b, ht6b, p5288_1, u0elo2]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4543, hlam, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h5231, hlam, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h5233, hlam, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              rcases p5288_3 (m.d 0 1) (by simp) with h5308 | h5308
                                                              · linarith only [h2678, h5308, hlam]
                                                              · linarith only [h4542, h5308, hlam]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4542, h5270, h5281, h5285, h5287, hc56, hlam, hphi, ht0b, ht6b, p5288_1, u0elo3]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4543, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p5288_1, u0elo3]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h2678, h4542, h5270, h5281, h5285, h5287, hc56, hlam, hphi, ht0b, ht6b, p5288_1, u0elo3]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4272, h4542, h5270, h5281, h5285, h5287, hc56, hlam, hphi, ht0b, ht6b, p5288_1, u0elo3]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              rcases p5288_3 (m.d 0 1) (by simp) with h5316 | h5316
                                                              · linarith only [h3738, h5316, hlam]
                                                              · linarith only [h4542, h5316, hlam]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4542, h5270, h5281, h5285, h5287, hc56, hlam, hphi, ht0b, ht6b, p5288_1, u0elo4]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4543, h5281, h5285, h5287, hc56, hlam, hphi, ht0b, ht6b, p5288_1, u0elo4]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h2678, h4542, h5270, h5281, h5285, h5287, hc56, hlam, hphi, ht0b, ht6b, p5288_1, u0elo4]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h5236, hlam, p5288_1]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              rcases p5288_3 (m.d 0 1) (by simp) with h5324 | h5324
                                                              · linarith only [h4272, h5324, hlam]
                                                              · linarith only [h4542, h5324, hlam]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h4542, hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h5230, hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h5235, hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h5237, hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [h5238, hlam, p5288_0]
                                                            · obtain ⟨p5288_0, p5288_1, p5288_2, p5288_3⟩ := h5288c
                                                              linarith only [hlam, p5288_0]
                                                          · linarith only [h5287, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h2678, h4542, h5239, h5240, h5270, h5277, h5283, h5286, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                      · linarith only [h2678, h5239, h5240, h5277, h5285, hc01, hc46, hlam, hphi, ht12, ht23, ht34]
                                                    · linarith only [h2678, h5239, h5240, h5277, h5284, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                                  · linarith only [h4543, h5048, h5283, hc23, hc56, hlam, hphi, ht34, ht45]
                                                · linarith only [h2678, h4542, h5236, h5239, h5240, h5270, h5281, h5282, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                              · linarith only [h5281, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4272, h5276, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4542, h5270, h5275, hc26, hlam, hphi, u6elo3]
                                · linarith only [h2678, h5239, h5270, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h4543, h5048, h5239, hc12, hc25, hlam, hphi]
                          · linarith only [h5048, h5238, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                        · linarith only [h5237, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5346 | h5346
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5347 | h5347
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5348 | h5348
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5349 | h5349
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5350 | h5350
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5351 | h5351
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5352 | h5352
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5353 | h5353
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5354 | h5354
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5355 | h5355
                                          · linarith only [h2678, h4542, h4543, h5231, h5350, h5355, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5357 | h5357
                                            · linarith only [h4543, h4544, h5233, h5348, h5351, h5355, h5357, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5359 | h5359
                                              · linarith only [h4543, h4544, h5348, h5351, h5355, h5359, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h5359, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h5354, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h5353, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4542, h5231, h5350, h5351, h5352, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5365 | h5365
                                    · linarith only [h2678, h4542, h5233, h5350, h5351, h5365, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5367 | h5367
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5368 | h5368
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5369 | h5369
                                          · linarith only [h4543, h5351, h5369, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5371 | h5371
                                            · linarith only [h2678, h4542, h4543, h4544, h5349, h5350, h5365, h5371, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5373 | h5373
                                              · linarith only [h4543, h4544, h5349, h5373, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                              · linarith only [h5373, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4272, h5368, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h4542, h5350, h5367, hc26, hlam, hphi, u6elo3]
                                · linarith only [h5350, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5379 | h5379
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5380 | h5380
                                  · linarith only [h5231, h5235, h5348, h5349, h5380, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5382 | h5382
                                    · linarith only [h2678, h4542, h5233, h5379, h5380, h5382, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5384 | h5384
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5385 | h5385
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5386 | h5386
                                          · linarith only [h4543, h5380, h5386, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5388 | h5388
                                            · linarith only [h2678, h4542, h4543, h5379, h5382, h5388, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5390 | h5390
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5391 | h5391
                                                · linarith only [h4543, h4544, h5236, h5386, h5391, hc23, hc34, hlam, hphi]
                                                · linarith only [h4543, h4544, h5390, h5391, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                              · linarith only [h5390, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                        · linarith only [h4272, h5385, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h5384, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                · linarith only [h2678, h5348, h5379, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                            · linarith only [h0, h4542, h4543, h5348, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
                          · linarith only [h5347, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h4544, h5346, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                    · linarith only [h5235, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
              · linarith only [h5230, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5403 | h5403
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5404 | h5404
            · rcases m.htr 0 2 6 (by decide) (by decide) with h5405 | h5405
              · rcases m.htr 0 3 4 (by decide) (by decide) with h5406 | h5406
                · rcases m.htr 0 3 5 (by decide) (by decide) with h5407 | h5407
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5408 | h5408
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5409 | h5409
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5410 | h5410
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5411 | h5411
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5412 | h5412
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5413 | h5413
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5414 | h5414
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5415 | h5415
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5416 | h5416
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5417 | h5417
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5418 | h5418
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5419 | h5419
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5420 | h5420
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5421 | h5421
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5422 | h5422
                                                · linarith only [h4543, h5403, h5412, h5422, hc12, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                                · linarith only [h4543, h5403, h5409, h5412, h5422, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                              · linarith only [h4272, h4543, h5403, h5409, h5421, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h4272, h4543, h5403, h5407, h5409, h5420, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                          · linarith only [h4543, h5406, h5419, hlam]
                                        · linarith only [h5418, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h4272, h4542, h4543, h5403, h5409, h5412, h5414, h5417, hc26, hlam, hphi, u6elo3]
                                    · linarith only [h4543, h5403, h5407, h5409, h5412, h5416, hlam]
                                  · linarith only [h4543, h5403, h5406, h5412, h5415, hlam]
                                · linarith only [h4272, h4542, h4543, h5403, h5409, h5412, h5414, hc16, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · linarith only [h4543, h5403, h5412, h5413, hlam]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5434 | h5434
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5435 | h5435
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5436 | h5436
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5437 | h5437
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5438 | h5438
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5439 | h5439
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5440 | h5440
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5441 | h5441
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5442 | h5442
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5443 | h5443
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5444 | h5444
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5445 | h5445
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5446 | h5446
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h5447 | h5447
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h5448 | h5448
                                                          · linarith only [h5403, h5440, h5445, h5448, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                                                          · linarith only [h5448, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h5435, h5444, h5447, hc35, hlam, hphi, ht56, u6elo1]
                                                      · linarith only [h5446, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h5403, h5412, h5443, h5445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                                  · linarith only [h5444, hc25, hlam, hphi, ht56, u6elo5]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5455 | h5455
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5456 | h5456
                                                    · linarith only [h5440, h5443, h5456, hlam]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5458 | h5458
                                                      · linarith only [h5409, h5440, h5443, h5458, hc46, hlam, hphi, ht0b, ht6b, u0elo3]
                                                      · linarith only [h5458, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h5455, hc25, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h3738, h5412, h5434, h5442, hc01, hc36, hlam, hphi, ht12, ht23]
                                            · linarith only [h3738, h4542, h5412, h5434, h5439, h5441, hc35, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h3738, h4542, h5412, h5434, h5439, h5440, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4272, h5439, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                                      · linarith only [h2678, h5438, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4542, h5407, h5435, h5437, hc26, hlam, hphi, ht0b, ht6b, u0elo4]
                                  · linarith only [h3738, h4542, h5406, h5412, h5434, h5435, h5436, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h3738, h4542, h5434, h5435, hc16, hlam, hphi, u6elo2]
                              · linarith only [h0, h5403, h5434, hlam]
                          · linarith only [h5411, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h5410, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5473 | h5473
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5474 | h5474
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5475 | h5475
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5476 | h5476
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5477 | h5477
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5478 | h5478
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5479 | h5479
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5480 | h5480
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5481 | h5481
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5482 | h5482
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5483 | h5483
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5484 | h5484
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5485 | h5485
                                                · linarith only [h3738, h4542, h5403, h5409, h5477, h5484, h5485, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5487 | h5487
                                                  · linarith only [h4543, h5404, h5475, h5487, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                                  · linarith only [h5485, h5487, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                              · linarith only [h4543, h5484, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h4543, h5407, h5483, hlam]
                                          · linarith only [h4543, h5406, h5482, hlam]
                                        · linarith only [h4272, h4542, h5477, h5481, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h3738, h4542, h4543, h5404, h5409, h5475, h5477, h5480, hc26, hlam, hphi, u6elo3]
                                    · linarith only [h4543, h5404, h5407, h5475, h5479, hlam]
                                  · linarith only [h4543, h5404, h5406, h5409, h5475, h5478, hlam]
                                · linarith only [h5477, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h4543, h5403, h5475, h5476, hlam]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5499 | h5499
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5500 | h5500
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5501 | h5501
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5502 | h5502
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5503 | h5503
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5504 | h5504
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5505 | h5505
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5506 | h5506
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5507 | h5507
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5508 | h5508
                                                · linarith only [h3738, h4542, h5403, h5409, h5500, h5507, h5508, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5510 | h5510
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5511 | h5511
                                                    · linarith only [h5403, h5409, h5505, h5511, hlam]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5513 | h5513
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h5514 | h5514
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h5515 | h5515
                                                          · rcases h0bigk with h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c | h5516c
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h0, hlam, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h2678, hlam, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h3738, hlam, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h4272, hlam, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h0, h5475, hc06, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h0, h5475, hc01, hc23, hlam, hphi, ht12, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h4543, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h0, h3738, h4542, h5475, h5500, h5507, h5513, h5515, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h0, h4272, h4542, h5475, h5500, h5507, h5513, h5515, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              rcases p5516_3 (m.d 0 1) (by simp) with h5528 | h5528
                                                              · linarith only [h0, h5528, hlam]
                                                              · linarith only [h4542, h5528, hlam]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h4542, h5500, h5507, h5513, h5515, hc56, hlam, hphi, ht0b, ht6b, p5516_1, u0elo2]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h0, h4542, h5500, h5507, h5513, h5515, hc56, hlam, hphi, ht0b, ht6b, p5516_1, u0elo2]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h3738, h4542, h5500, h5507, h5513, h5515, hc56, hlam, hphi, ht0b, ht6b, p5516_1, u0elo2]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h3738, h4542, h5409, h5500, h5507, h5513, h5515, hc56, hlam, hphi, ht0b, ht6b, p5516_1, u0elo2]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              rcases p5516_3 (m.d 0 1) (by simp) with h5536 | h5536
                                                              · linarith only [h2678, h5536, hlam]
                                                              · linarith only [h4542, h5536, hlam]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h4542, h5500, h5507, h5513, h5515, hc56, hlam, hphi, ht0b, ht6b, p5516_1, u0elo3]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h5403, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h5406, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h5409, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              rcases p5516_3 (m.d 0 1) (by simp) with h5544 | h5544
                                                              · linarith only [h3738, h5544, hlam]
                                                              · linarith only [h4542, h5544, hlam]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h0, h4542, h5404, h5475, h5500, h5507, h5513, h5515, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h5404, hlam, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h5407, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h0, h3738, h4542, h5404, h5475, h5500, h5507, h5513, h5515, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p5516_1]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              rcases p5516_3 (m.d 0 1) (by simp) with h5552 | h5552
                                                              · linarith only [h4272, h5552, hlam]
                                                              · linarith only [h4542, h5552, hlam]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h4542, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h5405, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h5408, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h5473, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [h5474, hlam, p5516_0]
                                                            · obtain ⟨p5516_0, p5516_1, p5516_2, p5516_3⟩ := h5516c
                                                              linarith only [hlam, p5516_0]
                                                          · linarith only [h5515, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h3738, h4542, h5475, h5499, h5500, h5510, h5514, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                      · linarith only [h5513, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h5508, h5510, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                              · linarith only [h3738, h5475, h5499, h5507, hc01, hc36, hlam, hphi, ht12, ht23]
                                            · linarith only [h3738, h5475, h5499, h5506, hc01, hc35, hlam, hphi, ht12, ht23]
                                          · linarith only [h3738, h4542, h5475, h5499, h5500, h5505, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4272, h4542, h5500, h5504, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h5503, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h5407, h5502, hlam]
                                  · linarith only [h2678, h5406, h5501, hlam]
                                · linarith only [h3738, h4542, h5499, h5500, hc16, hlam, hphi, u6elo2]
                              · linarith only [h0, h5403, h5499, hlam]
                          · linarith only [h5409, h5474, hc04, hlam, hphi, ht45, ht56, u6elo5]
                        · linarith only [h3738, h4542, h5473, hc16, hlam, hphi, u6elo4]
                    · linarith only [h5408, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · linarith only [h4543, h5404, h5407, hlam]
                · linarith only [h4543, h5403, h5406, hlam]
              · linarith only [h5405, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h5580 | h5580
              · rcases m.htr 0 3 4 (by decide) (by decide) with h5581 | h5581
                · rcases m.htr 0 3 5 (by decide) (by decide) with h5582 | h5582
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5583 | h5583
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5584 | h5584
                      · linarith only [h5403, h5404, h5584, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5586 | h5586
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5587 | h5587
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5588 | h5588
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5589 | h5589
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5590 | h5590
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5591 | h5591
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5592 | h5592
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5593 | h5593
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5594 | h5594
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5595 | h5595
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5596 | h5596
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5597 | h5597
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5598 | h5598
                                                · linarith only [h3738, h4542, h5403, h5584, h5590, h5597, h5598, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5600 | h5600
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5601 | h5601
                                                    · linarith only [h5403, h5404, h5595, h5598, h5601, hlam]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5603 | h5603
                                                      · linarith only [h5403, h5404, h5588, h5595, h5596, h5603, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                      · linarith only [h5603, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h5403, h5404, h5600, hc24, hc56, hlam, hphi, ht45]
                                              · linarith only [h4543, h5582, h5597, hc35, hlam, hphi, ht56, u6elo3]
                                            · linarith only [h4543, h5403, h5582, h5595, h5596, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                          · linarith only [h4543, h5581, h5595, hlam]
                                        · linarith only [h4272, h4542, h5590, h5594, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h4543, h5588, h5593, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h3738, h4542, h4543, h5403, h5582, h5588, h5590, h5592, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h2678, h4542, h5403, h5581, h5590, h5591, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h5590, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h4543, h5403, h5588, h5589, hlam]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5616 | h5616
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5617 | h5617
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5618 | h5618
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5619 | h5619
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5620 | h5620
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5621 | h5621
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5622 | h5622
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5623 | h5623
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5624 | h5624
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5625 | h5625
                                                · linarith only [h5403, h5584, h5625, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5627 | h5627
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5628 | h5628
                                                    · linarith only [h5403, h5404, h5622, h5625, h5628, hlam]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5630 | h5630
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h5631 | h5631
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h5632 | h5632
                                                          · rcases h0bigk with h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c | h5633c
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h0, hlam, p5633_1]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h2678, hlam, p5633_1]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h3738, hlam, p5633_1]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h4272, hlam, p5633_1]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h0, h5588, hc06, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, p5633_1]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5404, h5625, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5633_1]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h4543, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5404, h5625, hc04, hc45, hlam, hphi, p5633_1]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5404, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              rcases p5633_3 (m.d 0 1) (by simp) with h5645 | h5645
                                                              · linarith only [h0, h5645, hlam]
                                                              · linarith only [h4542, h5645, hlam]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h4542, h5617, h5624, h5630, h5632, hc56, hlam, hphi, ht0b, ht6b, p5633_1, u0elo2]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h0, h4542, h5617, h5624, h5630, h5632, hc56, hlam, hphi, ht0b, ht6b, p5633_1, u0elo2]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h3738, h4542, h5617, h5624, h5630, h5632, hc56, hlam, hphi, ht0b, ht6b, p5633_1, u0elo2]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h4272, h4542, h5617, h5624, h5630, h5632, hc56, hlam, hphi, ht0b, ht6b, p5633_1, u0elo2]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              rcases p5633_3 (m.d 0 1) (by simp) with h5653 | h5653
                                                              · linarith only [h2678, h5653, hlam]
                                                              · linarith only [h4542, h5653, hlam]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h4542, h5617, h5624, h5630, h5632, hc56, hlam, hphi, ht0b, ht6b, p5633_1, u0elo3]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5403, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5581, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5584, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              rcases p5633_3 (m.d 0 1) (by simp) with h5661 | h5661
                                                              · linarith only [h3738, h5661, hlam]
                                                              · linarith only [h4542, h5661, hlam]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h4542, h5617, h5624, h5630, h5632, hc56, hlam, hphi, ht0b, ht6b, p5633_1, u0elo4]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h0, h4542, h5617, h5624, h5630, h5632, hc56, hlam, hphi, ht0b, ht6b, p5633_1, u0elo4]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5582, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h3738, h4542, h5582, h5617, h5624, h5630, h5632, hc56, hlam, hphi, ht0b, ht6b, p5633_1, u0elo2]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              rcases p5633_3 (m.d 0 1) (by simp) with h5669 | h5669
                                                              · linarith only [h4272, h5669, hlam]
                                                              · linarith only [h4542, h5669, hlam]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h4542, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5580, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5583, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5586, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [h5587, hlam, p5633_0]
                                                            · obtain ⟨p5633_0, p5633_1, p5633_2, p5633_3⟩ := h5633c
                                                              linarith only [hlam, p5633_0]
                                                          · linarith only [h5625, h5632, hc25, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h3738, h4542, h5588, h5616, h5617, h5627, h5631, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                      · linarith only [h5630, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h5404, h5627, hc05, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h3738, h5588, h5616, h5624, hc01, hc36, hlam, hphi, ht12, ht23]
                                            · linarith only [h3738, h5588, h5616, h5623, hc01, hc35, hlam, hphi, ht12, ht23]
                                          · linarith only [h3738, h4542, h5588, h5616, h5621, h5622, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4272, h5621, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h5620, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h5582, h5619, hlam]
                                  · linarith only [h2678, h5581, h5618, hlam]
                                · linarith only [h3738, h5616, h5617, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4542, h5403, h5616, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
                          · linarith only [h5587, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h5586, hc04, hlam, hphi, ht45, ht56, u6elo4]
                    · linarith only [h5583, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5694 | h5694
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5695 | h5695
                      · linarith only [h4543, h5403, h5582, h5695, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5697 | h5697
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5698 | h5698
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5699 | h5699
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5700 | h5700
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5701 | h5701
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5702 | h5702
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5703 | h5703
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5704 | h5704
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5705 | h5705
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5706 | h5706
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5707 | h5707
                                            · linarith only [h4543, h5403, h5582, h5699, h5707, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                            · linarith only [h4543, h5403, h5699, h5703, h5706, h5707, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                          · linarith only [h4543, h5581, h5706, hlam]
                                        · linarith only [h5705, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h5582, h5703, h5704, hc03, hc36, hlam, hphi]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5713 | h5713
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5714 | h5714
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5715 | h5715
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5716 | h5716
                                            · linarith only [h5699, h5703, h5716, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5718 | h5718
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5719 | h5719
                                                · linarith only [h4543, h5403, h5695, h5699, h5703, h5719, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5721 | h5721
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5722 | h5722
                                                    · linarith only [h4543, h5403, h5699, h5703, h5715, h5719, h5722, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                    · linarith only [h4543, h5403, h5699, h5703, h5715, h5722, hc34, hc45, hlam, hphi]
                                                  · linarith only [h4543, h5403, h5715, h5716, h5721, hc34, hc56, hlam, hphi, ht45]
                                              · linarith only [h4543, h5403, h5715, h5718, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                          · linarith only [h3738, h4543, h5403, h5581, h5715, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                        · linarith only [h4272, h5714, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h4543, h5403, h5699, h5713, hc24, hlam, hphi, ht45, ht56, u6elo3]
                                  · linarith only [h3738, h4542, h4543, h5403, h5581, h5699, h5701, h5702, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h5701, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h4543, h5403, h5699, h5700, hlam]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5733 | h5733
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5734 | h5734
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5735 | h5735
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5736 | h5736
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5737 | h5737
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5738 | h5738
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5739 | h5739
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5740 | h5740
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5741 | h5741
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5742 | h5742
                                                · linarith only [h4543, h5403, h5582, h5736, h5742, hc13, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5744 | h5744
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5745 | h5745
                                                    · linarith only [h4543, h5403, h5582, h5739, h5740, h5742, h5745, hlam]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5747 | h5747
                                                      · linarith only [h4543, h5403, h5582, h5699, h5736, h5739, h5747, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                      · linarith only [h5747, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h4543, h5403, h5582, h5740, h5744, hc24, hc56, hlam, hphi, ht45]
                                              · linarith only [h5699, h5741, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h0, h5699, h5740, hc01, hc35, hlam, hphi, ht12, ht23]
                                          · linarith only [h4543, h5403, h5582, h5699, h5736, h5739, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                        · linarith only [h5738, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h3738, h4542, h4543, h5403, h5582, h5734, h5736, h5737, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5756 | h5756
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5757 | h5757
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5758 | h5758
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5759 | h5759
                                            · linarith only [h0, h4542, h5699, h5734, h5736, h5759, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                            · linarith only [h3738, h4542, h5699, h5733, h5734, h5759, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h3738, h4542, h5699, h5733, h5734, h5758, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h5757, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h3738, h4542, h5699, h5733, h5734, h5756, hc26, hlam, hphi, u6elo3]
                                  · linarith only [h3738, h4542, h5581, h5699, h5733, h5734, h5735, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h3738, h5733, h5734, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4542, h5403, h5733, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
                          · linarith only [h5698, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h3738, h4542, h5697, hc16, hlam, hphi, u6elo4]
                    · linarith only [h4543, h5694, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                · linarith only [h4543, h5403, h5581, hlam]
              · linarith only [h5403, h5580, hc24, hlam, hphi, ht45, ht56, u6elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5773 | h5773
            · rcases m.htr 0 2 6 (by decide) (by decide) with h5774 | h5774
              · rcases m.htr 0 3 4 (by decide) (by decide) with h5775 | h5775
                · rcases m.htr 0 3 5 (by decide) (by decide) with h5776 | h5776
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5777 | h5777
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5778 | h5778
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5779 | h5779
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5780 | h5780
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5781 | h5781
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5782 | h5782
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5783 | h5783
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5784 | h5784
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5785 | h5785
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5786 | h5786
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5787 | h5787
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5788 | h5788
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5789 | h5789
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5790 | h5790
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5791 | h5791
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5792 | h5792
                                                  · linarith only [h5403, h5773, h5781, h5788, h5792, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                                  · linarith only [h5792, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h4272, h5403, h5773, h5775, h5778, h5791, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                              · linarith only [h4543, h5790, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h4272, h4542, h5403, h5773, h5776, h5783, h5788, h5789, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                          · linarith only [h4272, h4542, h4543, h5773, h5775, h5783, h5788, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                                        · linarith only [h4272, h4542, h5783, h5787, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h4272, h4542, h5403, h5773, h5782, h5783, h5784, h5786, hc26, hlam, hphi, u6elo3]
                                    · linarith only [h5403, h5773, h5776, h5782, h5784, h5785, hlam]
                                  · linarith only [h2678, h4542, h5775, h5783, h5784, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h5783, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h4272, h4543, h5773, h5781, h5782, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5805 | h5805
                              · linarith only [h4272, h4542, h5403, h5773, h5781, h5805, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5807 | h5807
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5808 | h5808
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5809 | h5809
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5810 | h5810
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5811 | h5811
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5812 | h5812
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5813 | h5813
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5814 | h5814
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5815 | h5815
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5816 | h5816
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5817 | h5817
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5818 | h5818
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h5819 | h5819
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h5820 | h5820
                                                          · linarith only [h5775, h5817, h5820, hc56, hlam, hphi, ht0b, ht6b, u0elo2]
                                                          · linarith only [h5820, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h5807, h5816, h5819, hc35, hlam, hphi, ht56, u6elo1]
                                                      · linarith only [h5818, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5825 | h5825
                                                      · linarith only [h5775, h5778, h5817, h5825, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                                      · linarith only [h5825, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h5816, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h0, h5805, h5815, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                              · linarith only [h5810, h5814, hc23, hlam, hphi, ht34, ht45, ht56, u6elo1]
                                            · linarith only [h0, h5805, h5812, h5813, hc01, hc35, hlam, hphi, ht12, ht23]
                                          · linarith only [h0, h4542, h5781, h5810, h5812, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4272, h4542, h5810, h5811, hc36, hlam, hphi, u6elo5]
                                      · linarith only [h2678, h5810, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h2678, h4542, h5776, h5809, hc16, hlam, hphi, ht0b, ht6b, u0elo4]
                                  · linarith only [h0, h4542, h5775, h5781, h5807, h5808, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h0, h5807, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                          · linarith only [h4272, h4542, h5780, hc16, hlam, hphi, u6elo5]
                        · linarith only [h4272, h4542, h5403, h5773, h5779, hc16, hlam, hphi, u6elo4]
                      · linarith only [h5403, h5773, h5778, hlam]
                    · linarith only [h5777, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · linarith only [h5403, h5773, h5775, h5776, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h5843 | h5843
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5844 | h5844
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5845 | h5845
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5846 | h5846
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5847 | h5847
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5848 | h5848
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5849 | h5849
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5850 | h5850
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5851 | h5851
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5852 | h5852
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5853 | h5853
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5854 | h5854
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5855 | h5855
                                          · linarith only [h5775, h5843, h5848, h5855, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                          · linarith only [h4272, h4542, h4543, h5773, h5850, h5851, h5855, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h4272, h4542, h5850, h5854, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h5853, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h4272, h4542, h4543, h5773, h5775, h5850, h5851, h5852, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5861 | h5861
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5862 | h5862
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5863 | h5863
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5864 | h5864
                                          · linarith only [h2678, h4542, h5850, h5851, h5864, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5866 | h5866
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5867 | h5867
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5868 | h5868
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5869 | h5869
                                                  · linarith only [h4543, h5773, h5848, h5851, h5869, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                  · linarith only [h5869, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h4272, h4543, h5773, h5845, h5864, h5868, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                              · linarith only [h4272, h4542, h4543, h5773, h5850, h5867, hc26, hlam, hphi, u6elo3]
                                            · linarith only [h4272, h4542, h4543, h5773, h5843, h5850, h5866, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                        · linarith only [h4272, h4542, h5850, h5863, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h4272, h4542, h4543, h5773, h5848, h5850, h5862, hc26, hlam, hphi, u6elo3]
                                    · linarith only [h4543, h5773, h5843, h5848, h5861, hlam]
                                · linarith only [h5403, h5849, h5850, hc04, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h4272, h4542, h4543, h5773, h5848, h5849, hc16, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5880 | h5880
                              · linarith only [h4272, h4542, h5403, h5773, h5848, h5880, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5882 | h5882
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5883 | h5883
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5884 | h5884
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5885 | h5885
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5886 | h5886
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5887 | h5887
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5888 | h5888
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5889 | h5889
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5890 | h5890
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5891 | h5891
                                                  · linarith only [h4543, h5773, h5775, h5848, h5883, h5891, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                  · linarith only [h5888, h5891, hc35, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h0, h4542, h5880, h5882, h5889, h5890, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                              · linarith only [h4543, h5775, h5848, h5883, h5889, hc02, hc36, hlam, hphi, ht23]
                                            · linarith only [h4272, h4542, h4543, h5773, h5775, h5848, h5882, h5883, h5888, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h5848, h5883, h5887, hlam]
                                        · linarith only [h4272, h4542, h5882, h5886, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h4272, h4542, h4543, h5773, h5775, h5882, h5883, h5885, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h5775, h5843, h5883, h5884, hlam]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5901 | h5901
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5902 | h5902
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5903 | h5903
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5904 | h5904
                                          · linarith only [h0, h4542, h5848, h5882, h5883, h5904, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                          · linarith only [h0, h4542, h5848, h5882, h5904, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4272, h4542, h5882, h5903, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h0, h4542, h5848, h5882, h5902, hc26, hlam, hphi, u6elo3]
                                    · linarith only [h0, h4542, h5843, h5848, h5882, h5901, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h0, h4542, h5882, hc16, hlam, hphi, u6elo2]
                          · linarith only [h5847, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h5846, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h4543, h5773, h5775, h5845, hlam]
                    · linarith only [h4543, h5844, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                  · linarith only [h4543, h5773, h5843, hlam]
              · linarith only [h4272, h4542, h5773, h5774, hc16, hlam, hphi, u6elo2]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h5917 | h5917
              · rcases m.htr 0 3 4 (by decide) (by decide) with h5918 | h5918
                · rcases m.htr 0 3 5 (by decide) (by decide) with h5919 | h5919
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h5920 | h5920
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h5921 | h5921
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5922 | h5922
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5923 | h5923
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5924 | h5924
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5925 | h5925
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5926 | h5926
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5927 | h5927
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5928 | h5928
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5929 | h5929
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5930 | h5930
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5931 | h5931
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5932 | h5932
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5933 | h5933
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5934 | h5934
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5935 | h5935
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5936 | h5936
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5937 | h5937
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h5938 | h5938
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h5939 | h5939
                                                          · linarith only [h5918, h5936, h5939, hc56, hlam, hphi, ht0b, ht6b, u0elo2]
                                                          · linarith only [h5939, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h5926, h5935, h5938, hc35, hlam, hphi, ht56, u6elo1]
                                                      · linarith only [h5937, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5944 | h5944
                                                      · linarith only [h5921, h5936, h5944, hc46, hlam, hphi, ht0b, ht6b, u0elo3]
                                                      · linarith only [h5944, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h5773, h5935, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                                                · linarith only [h5403, h5921, h5934, hlam]
                                              · linarith only [h5403, h5931, h5933, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h4543, h5919, h5932, hlam]
                                          · linarith only [h4543, h5918, h5931, hlam]
                                        · linarith only [h5930, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h5929, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4542, h5403, h5919, h5925, h5926, h5927, h5928, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h4543, h5918, h5924, h5927, hlam]
                                · linarith only [h5926, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4543, h5924, h5925, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5958 | h5958
                              · linarith only [h0, h4542, h5403, h5924, h5958, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5960 | h5960
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5961 | h5961
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5962 | h5962
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h5963 | h5963
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h5964 | h5964
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5965 | h5965
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5966 | h5966
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h5967 | h5967
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5968 | h5968
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h5969 | h5969
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5970 | h5970
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5971 | h5971
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h5972 | h5972
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h5973 | h5973
                                                          · linarith only [h5918, h5970, h5973, hc56, hlam, hphi, ht0b, ht6b, u0elo2]
                                                          · linarith only [h5973, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h5960, h5969, h5972, hc35, hlam, hphi, ht56, u6elo1]
                                                      · linarith only [h5971, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h5978 | h5978
                                                      · linarith only [h5918, h5921, h5970, h5978, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                                      · linarith only [h5978, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h5969, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h0, h5918, h5921, h5958, h5968, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                              · linarith only [h0, h4542, h5958, h5960, h5965, h5967, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                            · linarith only [h0, h4542, h5958, h5960, h5965, h5966, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h4543, h5918, h5965, hlam]
                                        · linarith only [h4272, h5964, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h2678, h5963, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4542, h5919, h5958, h5960, h5961, h5962, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h2678, h5918, h5961, hlam]
                                · linarith only [h0, h4542, h5960, hc16, hlam, hphi, u6elo2]
                          · linarith only [h5773, h5923, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                        · linarith only [h5922, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h5993 | h5993
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h5994 | h5994
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h5995 | h5995
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h5996 | h5996
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h5997 | h5997
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h5998 | h5998
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5999 | h5999
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6000 | h6000
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6001 | h6001
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6002 | h6002
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6003 | h6003
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6004 | h6004
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6005 | h6005
                                                · linarith only [h0, h4542, h5403, h5921, h5996, h5997, h6004, h6005, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6007 | h6007
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6008 | h6008
                                                    · linarith only [h0, h4542, h5403, h5918, h5921, h5997, h6004, h6005, h6008, hc36, hlam, hphi, ht0b, ht6b, u0elo4]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h6010 | h6010
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h6011 | h6011
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h6012 | h6012
                                                          · rcases h0bigk with h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c | h6013c
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h0, hlam, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h2678, hlam, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h3738, hlam, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h4272, hlam, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h0, h5403, h6005, hc06, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5403, h6005, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h4543, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5403, hlam, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5773, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h4542, h5403, h5997, h6004, h6005, h6010, h6012, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h4542, h4543, h5995, h5997, h6004, h6010, h6012, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h0, h4542, h4543, h5995, h5997, h6004, h6010, h6012, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h0, h4542, h4543, h5403, h5995, h5997, h6004, h6010, h6012, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h4272, h4542, h4543, h5995, h5997, h6004, h6010, h6012, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              rcases p6013_3 (m.d 0 1) (by simp) with h6031 | h6031
                                                              · linarith only [h2678, h6031, hlam]
                                                              · linarith only [h4542, h6031, hlam]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h4542, h5997, h6004, h6010, h6012, hc56, hlam, hphi, ht0b, ht6b, p6013_1, u0elo3]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h0, h4542, h5403, h5997, h6004, h6005, h6010, h6012, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5918, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5921, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              rcases p6013_3 (m.d 0 1) (by simp) with h6039 | h6039
                                                              · linarith only [h3738, h6039, hlam]
                                                              · linarith only [h4542, h6039, hlam]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h4542, h4543, h5919, h5995, h5997, h6004, h6010, h6012, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h0, h4542, h4543, h5919, h5995, h5997, h6004, h6010, h6012, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5919, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h3738, h4542, h4543, h5919, h5995, h5997, h6004, h6010, h6012, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6013_1]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              rcases p6013_3 (m.d 0 1) (by simp) with h6047 | h6047
                                                              · linarith only [h4272, h6047, hlam]
                                                              · linarith only [h4542, h6047, hlam]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h4542, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5917, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5920, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5993, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [h5994, hlam, p6013_0]
                                                            · obtain ⟨p6013_0, p6013_1, p6013_2, p6013_3⟩ := h6013c
                                                              linarith only [hlam, p6013_0]
                                                          · linarith only [h6005, h6012, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                                        · linarith only [h0, h4542, h5403, h5997, h6005, h6007, h6008, h6011, hc34, hc45, hlam, hphi]
                                                      · linarith only [h6010, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h5773, h6007, hc05, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h4543, h6004, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h4543, h5919, h6003, hlam]
                                          · linarith only [h4543, h5918, h6002, hlam]
                                        · linarith only [h4272, h6001, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h5403, h5996, h5998, h6000, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h4543, h5919, h5995, h5999, hlam]
                                  · linarith only [h4543, h5918, h5995, h5998, hlam]
                                · linarith only [h4543, h5995, h5997, hc03, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4542, h4543, h5995, h5996, hc16, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h6069 | h6069
                              · linarith only [h0, h4542, h5403, h5995, h6069, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h6071 | h6071
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h6072 | h6072
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6073 | h6073
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6074 | h6074
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6075 | h6075
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6076 | h6076
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6077 | h6077
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6078 | h6078
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6079 | h6079
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6080 | h6080
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6081 | h6081
                                                    · linarith only [h0, h4542, h5403, h5918, h5921, h6071, h6078, h6081, hc36, hlam, hphi, ht0b, ht6b, u0elo2]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h6083 | h6083
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h6084 | h6084
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h6085 | h6085
                                                          · rcases h0bigk with h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c | h6086c
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h0, hlam, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h2678, hlam, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h3738, hlam, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h4272, hlam, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h0, h6069, h6076, hc06, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5403, h5921, h6079, hc01, hc25, hlam, hphi, ht12, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h4543, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5403, hlam, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5773, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h4542, h5403, h5921, h6071, h6076, h6078, h6079, h6083, h6085, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h4542, h6071, h6078, h6083, h6085, hc56, hlam, hphi, ht0b, ht6b, p6086_1, u0elo2]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h0, h4542, h6071, h6078, h6083, h6085, hc56, hlam, hphi, ht0b, ht6b, p6086_1, u0elo2]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h3738, h4542, h6071, h6078, h6083, h6085, hc56, hlam, hphi, ht0b, ht6b, p6086_1, u0elo2]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h0, h4542, h5403, h5921, h6071, h6078, h6083, h6085, hc56, hlam, hphi, ht0b, ht6b, p6086_1, u0elo2]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              rcases p6086_3 (m.d 0 1) (by simp) with h6104 | h6104
                                                              · linarith only [h2678, h6104, hlam]
                                                              · linarith only [h4542, h6104, hlam]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h4542, h6071, h6078, h6083, h6085, hc56, hlam, hphi, ht0b, ht6b, p6086_1, u0elo3]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h0, h4542, h5921, h6071, h6078, h6083, h6085, hc56, hlam, hphi, ht0b, ht6b, p6086_1, u0elo4]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5918, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5921, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h4542, h5921, h6071, h6076, h6078, h6079, h6083, h6085, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h4542, h5921, h6071, h6076, h6078, h6079, h6083, h6085, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h0, h4542, h5921, h6071, h6076, h6078, h6079, h6083, h6085, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5919, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h3738, h4542, h5921, h6071, h6076, h6078, h6079, h6083, h6085, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6086_1]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              rcases p6086_3 (m.d 0 1) (by simp) with h6118 | h6118
                                                              · linarith only [h4272, h6118, hlam]
                                                              · linarith only [h4542, h6118, hlam]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h4542, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5917, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5920, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5993, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [h5994, hlam, p6086_0]
                                                            · obtain ⟨p6086_0, p6086_1, p6086_2, p6086_3⟩ := h6086c
                                                              linarith only [hlam, p6086_0]
                                                          · linarith only [h5921, h6085, hc05, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h0, h4542, h5403, h5921, h6071, h6076, h6079, h6080, h6084, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                                      · linarith only [h6083, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h6080, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h0, h4542, h6069, h6071, h6078, h6079, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                              · linarith only [h6078, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h0, h6069, h6076, h6077, hc01, hc35, hlam, hphi, ht12, ht23]
                                          · linarith only [h0, h4542, h5995, h6071, h6076, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4272, h4542, h6071, h6075, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h2678, h6074, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4542, h5919, h6069, h6071, h6072, h6073, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                  · linarith only [h2678, h4542, h5918, h6071, h6072, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                                · linarith only [h0, h4542, h6071, hc16, hlam, hphi, u6elo2]
                          · linarith only [h5994, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h5403, h5993, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                    · linarith only [h5920, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h6143 | h6143
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h6144 | h6144
                      · linarith only [h5918, h5919, h6144, hlam]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h6146 | h6146
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h6147 | h6147
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h6148 | h6148
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h6149 | h6149
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h6150 | h6150
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h6151 | h6151
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6152 | h6152
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6153 | h6153
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6154 | h6154
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6155 | h6155
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6156 | h6156
                                            · linarith only [h0, h4542, h5403, h5918, h5919, h6148, h6150, h6156, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                            · linarith only [h0, h4542, h4543, h6150, h6152, h6156, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                          · linarith only [h0, h4542, h4543, h5918, h6150, h6155, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                        · linarith only [h5918, h5919, h6152, h6154, hc34, hc56, hlam, hphi, ht45]
                                      · linarith only [h6153, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6162 | h6162
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6163 | h6163
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6164 | h6164
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6165 | h6165
                                            · linarith only [h6148, h6152, h6165, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6167 | h6167
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6168 | h6168
                                                · linarith only [h0, h4542, h5403, h6144, h6149, h6150, h6151, h6152, h6167, h6168, hc35, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6170 | h6170
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6171 | h6171
                                                    · linarith only [h5918, h6168, h6171, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h6173 | h6173
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h6174 | h6174
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h6175 | h6175
                                                          · rcases h0bigk with h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c | h6176c
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h0, hlam, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h2678, hlam, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h3738, hlam, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h4272, hlam, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h2678, h6152, h6171, hc06, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h5403, hc01, hc24, hlam, hphi, ht12, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h4543, hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h5403, hlam, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h5773, hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h4542, h4543, h6148, h6150, h6152, h6167, h6171, h6173, h6175, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h4542, h4543, h6148, h6150, h6152, h6167, h6171, h6173, h6175, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h4543, h6148, h6152, h6171, hc02, hc45, hlam, hphi, ht23, ht34, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h4543, h6148, h6152, h6171, hc04, hc45, hlam, hphi, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h5919, hlam, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              rcases p6176_3 (m.d 0 1) (by simp) with h6194 | h6194
                                                              · linarith only [h2678, h6194, hlam]
                                                              · linarith only [h4542, h6194, hlam]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h4542, h6150, h6167, h6173, h6175, hc56, hlam, hphi, ht0b, ht6b, p6176_1, u0elo3]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h0, h4542, h5403, h6149, h6150, h6151, h6152, h6167, h6171, h6173, h6175, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p6176_1]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h5918, hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h6144, hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              rcases p6176_3 (m.d 0 1) (by simp) with h6202 | h6202
                                                              · linarith only [h3738, h6202, hlam]
                                                              · linarith only [h4542, h6202, hlam]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h4542, h6150, h6167, h6173, h6175, hc56, hlam, hphi, ht0b, ht6b, p6176_1, u0elo4]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h0, h4542, h6150, h6167, h6173, h6175, hc56, hlam, hphi, ht0b, ht6b, p6176_1, u0elo4]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h5918, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p6176_1, u0elo4]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h3738, h4542, h6150, h6167, h6173, h6175, hc56, hlam, hphi, ht0b, ht6b, p6176_1, u0elo4]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              rcases p6176_3 (m.d 0 1) (by simp) with h6210 | h6210
                                                              · linarith only [h4272, h6210, hlam]
                                                              · linarith only [h4542, h6210, hlam]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h4542, hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h5917, hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h6143, hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h6146, hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [h6147, hlam, p6176_0]
                                                            · obtain ⟨p6176_0, p6176_1, p6176_2, p6176_3⟩ := h6176c
                                                              linarith only [hlam, p6176_0]
                                                          · linarith only [h0, h4542, h5403, h6149, h6150, h6151, h6152, h6167, h6171, h6173, h6175, hc46, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b]
                                                        · linarith only [h0, h4542, h5403, h6149, h6150, h6151, h6152, h6170, h6174, hlam]
                                                      · linarith only [h6173, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h5773, h6170, hc05, hlam, hphi, ht56, u6elo5]
                                              · linarith only [h4543, h6167, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h0, h4542, h4543, h5918, h6150, h6164, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                        · linarith only [h4272, h6163, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4542, h5403, h6149, h6150, h6151, h6162, hc26, hlam, hphi, u6elo3]
                                  · linarith only [h2678, h4542, h5918, h6150, h6151, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                                · linarith only [h6150, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4543, h6148, h6149, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h6230 | h6230
                              · linarith only [h0, h4542, h5403, h6148, h6230, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h6232 | h6232
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h6233 | h6233
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6234 | h6234
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6235 | h6235
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6236 | h6236
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6237 | h6237
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6238 | h6238
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6239 | h6239
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6240 | h6240
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6241 | h6241
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6242 | h6242
                                                    · linarith only [h5918, h5919, h6234, h6242, hc13, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h6244 | h6244
                                                      · linarith only [h5918, h5919, h6237, h6240, h6242, h6244, hc23, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                      · linarith only [h6244, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                  · linarith only [h6241, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h0, h4542, h6230, h6232, h6239, h6240, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                              · linarith only [h6148, h6239, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h6148, h6234, h6238, hlam]
                                          · linarith only [h5918, h5919, h6148, h6234, h6237, hlam]
                                        · linarith only [h6236, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h5403, h5918, h5919, h6234, h6235, hc01, hc36, hlam, hphi, ht12, ht23]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6254 | h6254
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6255 | h6255
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6256 | h6256
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6257 | h6257
                                            · linarith only [h2678, h4542, h6232, h6234, h6257, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                            · linarith only [h0, h4542, h6148, h6232, h6257, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                          · linarith only [h0, h4542, h5918, h6148, h6232, h6256, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                        · linarith only [h0, h4542, h6230, h6232, h6233, h6234, h6255, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h0, h4542, h6230, h6232, h6233, h6254, hc26, hlam, hphi, u6elo3]
                                  · linarith only [h2678, h4542, h5918, h6232, h6233, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h0, h4542, h6232, hc16, hlam, hphi, u6elo2]
                          · linarith only [h6147, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h5403, h6146, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                    · linarith only [h6143, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h6268 | h6268
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h6269 | h6269
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h6270 | h6270
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h6271 | h6271
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h6272 | h6272
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h6273 | h6273
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h6274 | h6274
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h6275 | h6275
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h6276 | h6276
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6277 | h6277
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6278 | h6278
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6279 | h6279
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6280 | h6280
                                          · linarith only [h0, h4542, h5773, h5918, h6268, h6273, h6275, h6280, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                          · linarith only [h0, h4542, h4543, h6275, h6276, h6280, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h4272, h4542, h6275, h6279, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h6278, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h5918, h6268, h6276, h6277, hlam]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6286 | h6286
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6287 | h6287
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6288 | h6288
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6289 | h6289
                                          · linarith only [h0, h4542, h5773, h5918, h6268, h6273, h6275, h6289, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6291 | h6291
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6292 | h6292
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6293 | h6293
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6294 | h6294
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6295 | h6295
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h6296 | h6296
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h6297 | h6297
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h6298 | h6298
                                                          · rcases h0bigk with h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c | h6299c
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h0, hlam, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h2678, hlam, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h3738, hlam, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4272, hlam, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h2678, h6276, hc06, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4542, h5773, hc16, hlam, hphi, ht0b, ht6b, p6299_1, u0elo4]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4543, hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h5403, hlam, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h5773, hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4542, h5773, h6273, h6275, h6276, h6291, h6292, h6296, hc34, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4542, h4543, h6273, h6275, h6276, h6292, h6296, hc34, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4543, h6273, h6276, hc02, hc34, hlam, hphi, ht23, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h5918, hlam, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4272, h4542, h4543, h6273, h6275, h6276, h6292, h6296, hc34, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              rcases p6299_3 (m.d 0 1) (by simp) with h6317 | h6317
                                                              · linarith only [h2678, h6317, hlam]
                                                              · linarith only [h4542, h6317, hlam]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4542, h6275, h6292, h6296, h6298, hc56, hlam, hphi, ht0b, ht6b, p6299_1, u0elo3]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h0, h4542, h6275, h6292, h6296, h6298, hc56, hlam, hphi, ht0b, ht6b, p6299_1, u0elo3]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h6268, hc35, hlam, hphi, ht0b, ht56, ht6b, p6299_1, u0elo3]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h0, h4542, h5773, h6275, h6292, h6296, h6298, hc56, hlam, hphi, ht0b, ht6b, p6299_1, u0elo3]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              rcases p6299_3 (m.d 0 1) (by simp) with h6325 | h6325
                                                              · linarith only [h3738, h6325, hlam]
                                                              · linarith only [h4542, h6325, hlam]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4542, h6275, h6292, h6296, h6298, hc56, hlam, hphi, ht0b, ht6b, p6299_1, u0elo4]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h0, h4542, h5773, h6273, h6275, h6276, h6291, h6292, h6296, h6298, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h6268, hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h6270, hlam, p6299_1]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              rcases p6299_3 (m.d 0 1) (by simp) with h6333 | h6333
                                                              · linarith only [h4272, h6333, hlam]
                                                              · linarith only [h4542, h6333, hlam]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h4542, hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h5917, hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h6269, hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h6271, hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [h6272, hlam, p6299_0]
                                                            · obtain ⟨p6299_0, p6299_1, p6299_2, p6299_3⟩ := h6299c
                                                              linarith only [hlam, p6299_0]
                                                          · linarith only [h6298, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h4542, h6275, h6294, h6297, hc35, hlam, hphi, ht56, u6elo0]
                                                      · linarith only [h0, h5773, h6273, h6276, h6291, h6296, hc01, hc46, hlam, hphi, ht12, ht23, ht34]
                                                    · linarith only [h0, h4542, h5773, h6273, h6275, h6276, h6291, h6294, h6295, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                  · linarith only [h0, h4542, h5773, h6275, h6292, h6294, hc36, hlam, hphi, u6elo5]
                                                · linarith only [h5403, h6270, h6293, hlam]
                                              · linarith only [h0, h5773, h6291, h6292, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                                            · linarith only [h4543, h6268, h6291, hlam]
                                        · linarith only [h4272, h4542, h6275, h6288, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h4543, h6273, h6287, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4542, h4543, h6268, h6273, h6275, h6286, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h5403, h6270, h6274, h6275, hc45, hlam, hphi, ht56, u6elo2]
                              · linarith only [h0, h4543, h6273, h6274, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h6355 | h6355
                              · linarith only [h0, h4542, h5403, h6273, h6355, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h6357 | h6357
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h6358 | h6358
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6359 | h6359
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6360 | h6360
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6361 | h6361
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6362 | h6362
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6363 | h6363
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6364 | h6364
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6365 | h6365
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6366 | h6366
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6367 | h6367
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h6368 | h6368
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h6369 | h6369
                                                        · linarith only [h5918, h6268, h6273, h6358, h6369, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                        · linarith only [h6369, hc35, hlam, hphi, ht56, u6elo5]
                                                      · linarith only [h5918, h6368, hc03, hlam, hphi, ht34, ht45, ht56, u6elo4]
                                                    · linarith only [h0, h5773, h5918, h6268, h6270, h6367, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                                  · linarith only [h0, h4542, h5773, h6357, h6364, h6366, hc36, hlam, hphi, u6elo5]
                                                · linarith only [h5918, h6268, h6270, h6273, h6355, h6358, h6365, hc12, hc23, hlam, hphi]
                                              · linarith only [h5918, h6273, h6358, h6364, hc03, hc36, hlam, hphi]
                                            · linarith only [h0, h5773, h5918, h6268, h6273, h6358, h6363, hc01, hc35, hlam, hphi, ht12, ht23]
                                          · linarith only [h6273, h6358, h6362, hlam]
                                        · linarith only [h4272, h4542, h6357, h6361, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h0, h4542, h5773, h5918, h6268, h6357, h6358, h6360, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h5918, h6268, h6358, h6359, hlam]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6382 | h6382
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6383 | h6383
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6384 | h6384
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6385 | h6385
                                          · linarith only [h0, h4542, h6273, h6357, h6358, h6385, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                          · linarith only [h0, h4542, h6273, h6357, h6385, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4272, h4542, h6357, h6384, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h0, h4542, h6273, h6357, h6383, hc26, hlam, hphi, u6elo3]
                                    · linarith only [h0, h4542, h6268, h6273, h6357, h6382, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                                · linarith only [h0, h4542, h6357, hc16, hlam, hphi, u6elo2]
                          · linarith only [h5773, h6272, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                        · linarith only [h6271, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h5918, h6268, h6270, hlam]
                    · linarith only [h6269, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h6396 | h6396
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h6397 | h6397
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h6398 | h6398
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h6399 | h6399
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h6400 | h6400
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h6401 | h6401
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h6402 | h6402
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h6403 | h6403
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6404 | h6404
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6405 | h6405
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6406 | h6406
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6407 | h6407
                                          · linarith only [h0, h4542, h4543, h5918, h6400, h6402, h6407, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                          · linarith only [h0, h4542, h4543, h6402, h6403, h6407, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h0, h4542, h4543, h6268, h6402, h6404, h6406, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h6405, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4542, h4543, h5918, h6402, h6403, h6404, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6413 | h6413
                                    · linarith only [h0, h4542, h4543, h6268, h6402, h6403, h6413, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6415 | h6415
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6416 | h6416
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6417 | h6417
                                          · linarith only [h2678, h4542, h6402, h6403, h6417, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6419 | h6419
                                            · linarith only [h6400, h6413, h6419, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6421 | h6421
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6422 | h6422
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6423 | h6423
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6424 | h6424
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h6425 | h6425
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h6426 | h6426
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h6427 | h6427
                                                          · rcases h0bigk with h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c | h6428c
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h0, hlam, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h2678, hlam, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h3738, hlam, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h4272, hlam, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h0, h4543, h6400, h6413, h6424, hc06, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h4543, h6400, hc01, hc13, hlam, hphi, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h4543, hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h5403, hlam, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h5773, hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h4542, h4543, h6400, h6402, h6421, h6425, h6427, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h2678, h4542, h6402, h6413, h6421, h6424, h6425, h6427, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h2678, h6413, h6424, hc02, hc34, hlam, hphi, ht23, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h5918, hlam, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h6268, hlam, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              rcases p6428_3 (m.d 0 1) (by simp) with h6446 | h6446
                                                              · linarith only [h2678, h6446, hlam]
                                                              · linarith only [h4542, h6446, hlam]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h4542, h6402, h6421, h6425, h6427, hc56, hlam, hphi, ht0b, ht6b, p6428_1, u0elo3]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h0, h4542, h5403, h6401, h6402, h6421, h6425, h6427, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h2678, h4542, h5403, h6401, h6402, h6421, h6425, h6427, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h0, h4542, h4543, h5403, h6268, h6401, h6402, h6421, h6425, h6427, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              rcases p6428_3 (m.d 0 1) (by simp) with h6454 | h6454
                                                              · linarith only [h3738, h6454, hlam]
                                                              · linarith only [h4542, h6454, hlam]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h4542, h6402, h6421, h6425, h6427, hc56, hlam, hphi, ht0b, ht6b, p6428_1, u0elo4]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h0, h4542, h5773, h6401, h6402, h6421, h6422, h6425, h6427, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h0, h4542, h4543, h5773, h6401, h6402, h6421, h6422, h6425, h6427, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h6397, hlam, p6428_1]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              rcases p6428_3 (m.d 0 1) (by simp) with h6462 | h6462
                                                              · linarith only [h4272, h6462, hlam]
                                                              · linarith only [h4542, h6462, hlam]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h4542, hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h5917, hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h6396, hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h6398, hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [h6399, hlam, p6428_0]
                                                            · obtain ⟨p6428_0, p6428_1, p6428_2, p6428_3⟩ := h6428c
                                                              linarith only [hlam, p6428_0]
                                                          · linarith only [h6427, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h4542, h6402, h6413, h6423, h6426, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                                      · linarith only [h0, h4542, h4543, h6398, h6400, h6402, h6413, h6421, h6424, h6425, hc36, hlam, hphi, u6elo0]
                                                    · linarith only [h3738, h6397, h6403, h6424, hlam]
                                                  · linarith only [h6423, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h5403, h6397, h6422, hlam]
                                              · linarith only [h0, h4542, h4543, h6402, h6421, hc26, hlam, hphi, u6elo3]
                                        · linarith only [h6416, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4542, h4543, h6400, h6402, h6415, hc26, hlam, hphi, u6elo3]
                                · linarith only [h5403, h6401, h6402, hc04, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h0, h4542, h4543, h6400, h6401, hc16, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h6482 | h6482
                              · linarith only [h0, h4542, h5403, h6400, h6482, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h6484 | h6484
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h6485 | h6485
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6486 | h6486
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6487 | h6487
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6488 | h6488
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6489 | h6489
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6490 | h6490
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6491 | h6491
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6492 | h6492
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6493 | h6493
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6494 | h6494
                                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h6495 | h6495
                                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h6496 | h6496
                                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h6497 | h6497
                                                          · rcases h0bigk with h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c | h6498c
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h0, hlam, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h2678, hlam, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h3738, hlam, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h4272, hlam, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h0, h6482, h6489, hc06, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h0, h6482, h6489, hc01, hc23, hlam, hphi, ht12, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h4543, hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h5403, hlam, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h5773, hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h4542, h4543, h5918, h6400, h6484, h6485, h6491, h6495, h6497, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h4542, h6484, h6491, h6495, h6497, hc56, hlam, hphi, ht0b, ht6b, p6498_1, u0elo2]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h6268, h6490, hc02, hc25, hlam, hphi, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h5918, hlam, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h6268, hlam, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h4542, h5918, h6400, h6484, h6485, h6491, h6495, h6497, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h4542, h5918, h6400, h6484, h6485, h6491, h6495, h6497, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h0, h4542, h5918, h6400, h6484, h6485, h6491, h6495, h6497, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h2678, h4542, h5918, h6400, h6484, h6485, h6491, h6495, h6497, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h4272, h4542, h5918, h6400, h6484, h6485, h6491, h6495, h6497, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              rcases p6498_3 (m.d 0 1) (by simp) with h6522 | h6522
                                                              · linarith only [h3738, h6522, hlam]
                                                              · linarith only [h4542, h6522, hlam]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h4542, h6484, h6491, h6495, h6497, hc56, hlam, hphi, ht0b, ht6b, p6498_1, u0elo4]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h0, h4542, h6484, h6491, h6495, h6497, hc56, hlam, hphi, ht0b, ht6b, p6498_1, u0elo4]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h0, h4542, h4543, h6268, h6400, h6484, h6485, h6491, h6494, h6495, h6497, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h6397, hlam, p6498_1]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              rcases p6498_3 (m.d 0 1) (by simp) with h6530 | h6530
                                                              · linarith only [h4272, h6530, hlam]
                                                              · linarith only [h4542, h6530, hlam]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h4542, hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h5917, hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h6396, hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h6398, hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [h6399, hlam, p6498_0]
                                                            · obtain ⟨p6498_0, p6498_1, p6498_2, p6498_3⟩ := h6498c
                                                              linarith only [hlam, p6498_0]
                                                          · linarith only [h6497, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h0, h4542, h4543, h6268, h6484, h6493, h6496, hlam]
                                                      · linarith only [h0, h4543, h6268, h6494, h6495, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo4]
                                                    · linarith only [h5918, h6397, h6494, hlam]
                                                  · linarith only [h6493, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h6397, h6482, h6492, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                              · linarith only [h0, h4543, h5918, h6400, h6485, h6491, hc01, hc36, hlam, hphi, ht12, ht23]
                                            · linarith only [h0, h4543, h5918, h6400, h6485, h6490, hc01, hc35, hlam, hphi, ht12, ht23]
                                          · linarith only [h6400, h6485, h6489, hlam]
                                        · linarith only [h6488, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4542, h4543, h5918, h6484, h6485, h6487, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h0, h4542, h4543, h5918, h6484, h6485, h6486, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6551 | h6551
                                    · linarith only [h0, h4542, h4543, h6268, h6484, h6485, h6551, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6553 | h6553
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6554 | h6554
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6555 | h6555
                                          · linarith only [h2678, h4542, h6484, h6485, h6555, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                          · linarith only [h0, h4542, h6400, h6484, h6555, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h4272, h6554, hc05, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4542, h6400, h6484, h6553, hc26, hlam, hphi, u6elo3]
                                · linarith only [h0, h4542, h6484, hc16, hlam, hphi, u6elo2]
                          · linarith only [h6399, hc05, hlam, hphi, ht56, u6elo5]
                        · linarith only [h6398, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h6563 | h6563
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h6564 | h6564
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h6565 | h6565
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h6566 | h6566
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h6567 | h6567
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h6568 | h6568
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6569 | h6569
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6570 | h6570
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6571 | h6571
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6572 | h6572
                                          · linarith only [h0, h4542, h4543, h5918, h6565, h6567, h6572, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                          · linarith only [h0, h4542, h4543, h6565, h6567, h6568, h6572, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h6571, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h6570, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                    · linarith only [h0, h4542, h4543, h5918, h6567, h6568, h6569, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6578 | h6578
                                    · linarith only [h0, h4542, h4543, h6268, h6567, h6568, h6578, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6580 | h6580
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6581 | h6581
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6582 | h6582
                                          · linarith only [h2678, h4542, h6567, h6568, h6582, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6584 | h6584
                                            · linarith only [h6565, h6578, h6584, hlam]
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6586 | h6586
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6587 | h6587
                                                · linarith only [h6397, h6563, h6566, h6587, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6589 | h6589
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6590 | h6590
                                                    · linarith only [h0, h4542, h5403, h6567, h6586, h6587, h6590, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                    · linarith only [h0, h4542, h4543, h6565, h6567, h6568, h6586, h6590, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                  · linarith only [h0, h4542, h4543, h6567, h6582, h6586, h6587, h6589, hc36, hlam, hphi, u6elo5]
                                              · linarith only [h0, h4542, h4543, h6567, h6586, hc26, hlam, hphi, u6elo3]
                                        · linarith only [h0, h4542, h4543, h6565, h6567, h6578, h6581, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h0, h4542, h4543, h6565, h6567, h6580, hc26, hlam, hphi, u6elo3]
                                · linarith only [h6567, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h4543, h6565, h6566, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h6599 | h6599
                              · linarith only [h0, h4542, h5403, h6565, h6599, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h6601 | h6601
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h6602 | h6602
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6603 | h6603
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6604 | h6604
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6605 | h6605
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6606 | h6606
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6607 | h6607
                                            · rcases m.htr 2 3 6 (by decide) (by decide) with h6608 | h6608
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6609 | h6609
                                                · rcases m.htr 2 5 6 (by decide) (by decide) with h6610 | h6610
                                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6611 | h6611
                                                    · linarith only [h3738, h4542, h6397, h6565, h6601, h6602, h6608, h6611, hc23, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                    · linarith only [h0, h4542, h4543, h5918, h6601, h6606, h6608, h6609, h6611, hc23, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                  · linarith only [h6610, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h0, h4542, h6599, h6601, h6608, h6609, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                              · linarith only [h6268, h6565, h6603, h6608, hc05, hlam, hphi, ht56, u6elo3]
                                            · linarith only [h0, h4543, h5918, h6565, h6602, h6603, h6607, hc01, hc15, hlam, hphi]
                                          · linarith only [h6565, h6602, h6606, hlam]
                                        · linarith only [h6605, hc15, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h4542, h4543, h5918, h6601, h6602, h6604, hc26, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h0, h4542, h4543, h5918, h6601, h6602, h6603, hc26, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6622 | h6622
                                    · linarith only [h0, h4542, h4543, h6268, h6601, h6602, h6622, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 1 3 6 (by decide) (by decide) with h6624 | h6624
                                      · rcases m.htr 1 5 6 (by decide) (by decide) with h6625 | h6625
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6626 | h6626
                                          · linarith only [h2678, h4542, h6601, h6602, h6626, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                          · linarith only [h0, h4542, h6565, h6601, h6626, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                        · linarith only [h0, h4542, h6565, h6601, h6622, h6625, hc26, hlam, hphi, u6elo5]
                                      · linarith only [h0, h4542, h6565, h6601, h6624, hc26, hlam, hphi, u6elo3]
                                · linarith only [h0, h6601, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                          · linarith only [h0, h4542, h4543, h5918, h6397, h6564, hc16, hlam, hphi, u6elo5]
                        · linarith only [h0, h4542, h4543, h5918, h6563, hc16, hlam, hphi, u6elo4]
                    · linarith only [h0, h4542, h4543, h6396, hc16, hlam, hphi, u6elo3]
              · linarith only [h0, h4542, h5917, hc16, hlam, hphi, u6elo2]
      · linarith only [h4542, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]

set_option maxHeartbeats 7918000 in
private theorem n8l_sBT8_M_LI_H_L_s1 (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h6elo := hb6.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0elo5 := h0elo (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h2678 | h2678
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2679 | h2679
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2680 | h2680
      · rcases m.htr 0 1 6 (by decide) (by decide) with h2681 | h2681
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2682 | h2682
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2683 | h2683
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2684 | h2684
              · rcases m.htr 0 2 6 (by decide) (by decide) with h2685 | h2685
                · rcases m.htr 0 3 4 (by decide) (by decide) with h2686 | h2686
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2687 | h2687
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2688 | h2688
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2689 | h2689
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2690 | h2690
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2691 | h2691
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2692 | h2692
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2693 | h2693
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2694 | h2694
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2695 | h2695
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2696 | h2696
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2697 | h2697
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2698 | h2698
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2699 | h2699
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2700 | h2700
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2701 | h2701
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2702 | h2702
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2703 | h2703
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2704 | h2704
                                                      · linarith only [h2678, h2692, h2699, h2704, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                                      · linarith only [h0, h2678, h2693, h2695, h2702, h2704, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                    · linarith only [h2703, hc25, hlam, hphi, ht56, u6elo5]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2708 | h2708
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2709 | h2709
                                                      · linarith only [h0, h2678, h2686, h2702, h2709, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2711 | h2711
                                                        · linarith only [h0, h2678, h2686, h2689, h2699, h2702, h2711, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                                        · linarith only [h2711, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h2708, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h2701, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h0, h2678, h2687, h2699, h2700, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                            · linarith only [h0, h2678, h2695, h2699, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · linarith only [h2698, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h2697, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h0, h2678, h2687, h2695, h2696, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2721 | h2721
                                      · linarith only [h0, h2678, h2686, h2695, h2721, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2723 | h2723
                                        · linarith only [h0, h2678, h2686, h2695, h2723, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                        · linarith only [h2723, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h2694, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h2683, h2693, hlam]
                              · linarith only [h0, h2682, h2692, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h2691, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h2690, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2731 | h2731
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2732 | h2732
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2733 | h2733
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2734 | h2734
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2735 | h2735
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2736 | h2736
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2737 | h2737
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2738 | h2738
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2739 | h2739
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2740 | h2740
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2741 | h2741
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2742 | h2742
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2743 | h2743
                                                  · linarith only [h2679, h2689, h2731, h2734, h2743, hc46, hlam, hphi, ht0b, ht6b, u0elo0]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2745 | h2745
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2746 | h2746
                                                      · linarith only [h2678, h2689, h2731, h2733, h2740, h2746, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2748 | h2748
                                                        · linarith only [h0, h2678, h2733, h2741, h2746, h2748, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                        · linarith only [h2689, h2731, h2748, hc34, hc45, hlam, hphi]
                                                    · linarith only [h2743, h2745, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                                · linarith only [h2742, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                              · linarith only [h0, h2678, h2687, h2740, h2741, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                            · linarith only [h0, h2678, h2736, h2740, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                          · linarith only [h2739, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h2738, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h0, h2678, h2687, h2736, h2737, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2758 | h2758
                                      · linarith only [h0, h2678, h2686, h2736, h2758, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2760 | h2760
                                        · linarith only [h0, h2678, h2687, h2758, h2760, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h2760, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h2735, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h2678, h2683, h2687, h2689, h2733, h2734, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                              · linarith only [h0, h2682, h2733, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h2689, h2731, h2732, hc46, hlam, hphi, u6elo5]
                          · linarith only [h2731, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h2686, h2688, hc34, hlam, hphi, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2769 | h2769
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2770 | h2770
                        · linarith only [h2686, h2687, h2770, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2772 | h2772
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2773 | h2773
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2774 | h2774
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2775 | h2775
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2776 | h2776
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2777 | h2777
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2778 | h2778
                                      · linarith only [h2678, h2687, h2778, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2780 | h2780
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2781 | h2781
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2782 | h2782
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2783 | h2783
                                              · linarith only [h2678, h2687, h2774, h2783, hlam]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2785 | h2785
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2786 | h2786
                                                  · linarith only [h2679, h2770, h2775, h2786, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2788 | h2788
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2789 | h2789
                                                      · linarith only [h2682, h2770, h2782, h2789, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2791 | h2791
                                                        · linarith only [h0, h2678, h2774, h2782, h2791, hc12, hc46, hlam, hphi, ht01, ht0b, ht6b]
                                                        · linarith only [h2791, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                                    · linarith only [h2783, h2788, hc23, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                                · linarith only [h2782, h2785, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                            · linarith only [h2686, h2687, h2782, hc23, hc35, hlam, hphi]
                                          · linarith only [h2778, h2781, hc13, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                        · linarith only [h2777, h2780, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                    · linarith only [h2686, h2687, h2777, hc13, hc35, hlam, hphi]
                                  · linarith only [h0, h2776, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h2683, h2775, hlam]
                              · linarith only [h0, h2682, h2774, hlam]
                            · linarith only [h2687, h2773, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                          · linarith only [h2683, h2772, hc24, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h2686, h2769, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2806 | h2806
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2807 | h2807
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2808 | h2808
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2809 | h2809
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2810 | h2810
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2811 | h2811
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2812 | h2812
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2813 | h2813
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2814 | h2814
                                    · linarith only [h2678, h2686, h2814, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2816 | h2816
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2817 | h2817
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2818 | h2818
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2819 | h2819
                                            · linarith only [h2678, h2682, h2686, h2816, h2819, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2821 | h2821
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2822 | h2822
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2823 | h2823
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2824 | h2824
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2825 | h2825
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2826 | h2826
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2827 | h2827
                                                          · linarith only [h0, h2678, h2811, h2821, h2827, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                                                          · linarith only [h2827, hc35, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h2686, h2826, hc03, hlam, hphi, ht34, ht45, ht56, u6elo4]
                                                      · linarith only [h2678, h2686, h2808, h2811, h2821, h2824, h2825, hc56, hlam, hphi, ht0b, ht6b, u0elo3]
                                                    · linarith only [h2824, hc25, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h0, h2679, h2808, h2819, h2821, h2823, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                                · linarith only [h2821, h2822, hc35, hlam, hphi, ht56, u6elo3]
                                              · linarith only [h2686, h2806, h2821, hc23, hc34, hlam, hphi]
                                          · linarith only [h2818, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h2817, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h2686, h2806, h2811, h2816, hc23, hc34, hlam, hphi]
                                  · linarith only [h0, h2813, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h2683, h2812, hlam]
                              · linarith only [h0, h2682, h2811, hlam]
                            · linarith only [h2810, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h2686, h2809, hc03, hlam, hphi, ht34, ht45, ht56, u6elo4]
                        · linarith only [h2686, h2806, h2808, hlam]
                      · linarith only [h2807, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2846 | h2846
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2847 | h2847
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2848 | h2848
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2849 | h2849
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2850 | h2850
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2851 | h2851
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2852 | h2852
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2853 | h2853
                                    · linarith only [h2678, h2686, h2853, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2855 | h2855
                                      · linarith only [h2678, h2806, h2855, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2857 | h2857
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2858 | h2858
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2859 | h2859
                                            · linarith only [h2678, h2682, h2686, h2857, h2859, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2861 | h2861
                                              · linarith only [h2678, h2806, h2850, h2861, hlam]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2863 | h2863
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2864 | h2864
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2865 | h2865
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2866 | h2866
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2867 | h2867
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2868 | h2868
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2869 | h2869
                                                            · linarith only [h2683, h2864, h2869, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                                                            · linarith only [h2869, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h2678, h2680, h2806, h2850, h2858, h2863, h2867, h2868, hc46, hlam, hphi, ht0b, ht6b, u0elo4]
                                                        · linarith only [h2678, h2806, h2850, h2863, h2866, h2867, hc36, hlam, hphi, u6elo4]
                                                      · linarith only [h0, h2678, h2679, h2686, h2847, h2850, h2863, h2866, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                                    · linarith only [h2865, hc25, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h0, h2679, h2847, h2859, h2863, h2864, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                                · linarith only [h2863, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h2858, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h2857, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h2852, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h2683, h2851, hlam]
                              · linarith only [h0, h2682, h2850, hlam]
                            · linarith only [h2806, h2849, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                          · linarith only [h2848, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2885 | h2885
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2886 | h2886
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h2887 | h2887
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h2888 | h2888
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h2889 | h2889
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2890 | h2890
                                    · linarith only [h2678, h2686, h2846, h2890, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2892 | h2892
                                      · linarith only [h2678, h2806, h2892, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h2894 | h2894
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h2895 | h2895
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2896 | h2896
                                            · linarith only [h2682, h2686, h2896, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2898 | h2898
                                              · linarith only [h2678, h2806, h2887, h2898, hlam]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h2900 | h2900
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2901 | h2901
                                                  · linarith only [h2678, h2683, h2686, h2847, h2887, h2900, h2901, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h2903 | h2903
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2904 | h2904
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2905 | h2905
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2906 | h2906
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2907 | h2907
                                                            · rcases h0bigk with h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h0, hlam, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h0, h2678, h2887, h2900, h2905, h2907, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h0, h2678, h2686, h2887, h2900, h2905, h2907, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h0, h2678, h2686, h2847, h2887, h2900, h2905, h2907, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                rcases p2908_3 (m.d 0 1) (by simp) with h2914 | h2914
                                                                · rcases p2908_3 (m.d 0 2) (by simp) with h2915 | h2915
                                                                  · rcases p2908_3 (m.d 0 3) (by simp) with h2916 | h2916
                                                                    · linarith only [h2678, h2916, hlam]
                                                                    · linarith only [h2846, h2916, hlam]
                                                                  · linarith only [h2685, h2915, hlam]
                                                                · linarith only [h2681, h2914, hlam]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2678, h2887, h2900, h2905, h2907, hc56, hlam, hphi, ht0b, ht6b, p2908_1, u0elo1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2678, h2887, h2900, h2905, h2907, hc56, hlam, hphi, ht0b, ht6b, p2908_1, u0elo1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2678, h2686, h2887, h2900, h2905, h2907, hc56, hlam, hphi, ht0b, ht6b, p2908_1, u0elo1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2678, h2686, h2847, h2887, h2900, h2905, h2907, hc56, hlam, hphi, ht0b, ht6b, p2908_1, u0elo1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                rcases p2908_3 (m.d 0 1) (by simp) with h2926 | h2926
                                                                · linarith only [h0, h2926, hlam]
                                                                · linarith only [h2681, h2926, hlam]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2678, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2682, hlam, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2686, hlam, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2806, hlam, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2686, h2847, h2904, hc06, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2679, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2683, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2847, h2904, hc03, hc34, hlam, hphi, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2847, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2846, h2847, h2904, h2905, h2907, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2680, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2684, hlam, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2678, h2887, h2900, h2905, h2907, hc56, hlam, hphi, ht0b, ht6b, p2908_1, u0elo4]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2678, h2686, h2847, h2887, h2900, h2904, h2905, h2907, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p2908_1]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                rcases p2908_3 (m.d 0 1) (by simp) with h2946 | h2946
                                                                · rcases p2908_3 (m.d 0 2) (by simp) with h2947 | h2947
                                                                  · rcases p2908_3 (m.d 0 3) (by simp) with h2948 | h2948
                                                                    · linarith only [h2806, h2948, hlam]
                                                                    · linarith only [h2846, h2948, hlam]
                                                                  · linarith only [h2685, h2947, hlam]
                                                                · linarith only [h2681, h2946, hlam]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2681, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2685, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2846, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2885, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [h2886, hlam, p2908_0]
                                                              · obtain ⟨p2908_0, p2908_1, p2908_2, p2908_3⟩ := h2908c
                                                                linarith only [hlam, p2908_0]
                                                            · linarith only [h2847, h2907, hc05, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h2680, h2686, h2847, h2895, h2904, h2906, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo4]
                                                        · linarith only [h2847, h2904, h2905, hc05, hlam, hphi, ht56, u6elo4]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h2962 | h2962
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h2963 | h2963
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h2964 | h2964
                                                            · rcases h0bigk with h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h0, hlam, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h0, h2678, h2887, h2900, h2962, h2964, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h0, h2678, h2686, h2887, h2900, h2962, h2964, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h0, h2678, h2686, h2847, h2887, h2900, h2962, h2964, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                rcases p2965_3 (m.d 0 1) (by simp) with h2971 | h2971
                                                                · rcases p2965_3 (m.d 0 2) (by simp) with h2972 | h2972
                                                                  · rcases p2965_3 (m.d 0 3) (by simp) with h2973 | h2973
                                                                    · linarith only [h2678, h2973, hlam]
                                                                    · linarith only [h2846, h2973, hlam]
                                                                  · linarith only [h2685, h2972, hlam]
                                                                · linarith only [h2681, h2971, hlam]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2678, h2887, h2900, h2962, h2964, hc56, hlam, hphi, ht0b, ht6b, p2965_1, u0elo1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2678, h2887, h2900, h2962, h2964, hc56, hlam, hphi, ht0b, ht6b, p2965_1, u0elo1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2678, h2686, h2887, h2900, h2962, h2964, hc56, hlam, hphi, ht0b, ht6b, p2965_1, u0elo1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2678, h2686, h2847, h2887, h2900, h2962, h2964, hc56, hlam, hphi, ht0b, ht6b, p2965_1, u0elo1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                rcases p2965_3 (m.d 0 1) (by simp) with h2983 | h2983
                                                                · linarith only [h0, h2983, hlam]
                                                                · linarith only [h2681, h2983, hlam]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2678, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2682, hlam, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2686, hlam, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2806, hlam, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2681, h2686, h2889, h2900, h2904, h2962, h2964, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2679, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2683, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2678, h2847, h2887, h2900, h2962, h2964, hc56, hlam, hphi, ht0b, ht6b, p2965_1, u0elo4]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2847, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                rcases p2965_3 (m.d 0 1) (by simp) with h2997 | h2997
                                                                · rcases p2965_3 (m.d 0 2) (by simp) with h2998 | h2998
                                                                  · rcases p2965_3 (m.d 0 3) (by simp) with h2999 | h2999
                                                                    · linarith only [h2686, h2999, hlam]
                                                                    · linarith only [h2846, h2999, hlam]
                                                                  · linarith only [h2685, h2998, hlam]
                                                                · linarith only [h2681, h2997, hlam]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2680, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2684, hlam, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h0, h2678, h2680, h2887, h2900, h2962, h2964, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h0, h2678, h2680, h2686, h2887, h2900, h2962, h2964, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b, p2965_1]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                rcases p2965_3 (m.d 0 1) (by simp) with h3009 | h3009
                                                                · rcases p2965_3 (m.d 0 2) (by simp) with h3010 | h3010
                                                                  · rcases p2965_3 (m.d 0 3) (by simp) with h3011 | h3011
                                                                    · linarith only [h2806, h3011, hlam]
                                                                    · linarith only [h2846, h3011, hlam]
                                                                  · linarith only [h2685, h3010, hlam]
                                                                · linarith only [h2681, h3009, hlam]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2681, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2685, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2846, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2885, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [h2886, hlam, p2965_0]
                                                              · obtain ⟨p2965_0, p2965_1, p2965_2, p2965_3⟩ := h2965c
                                                                linarith only [hlam, p2965_0]
                                                            · linarith only [h2678, h2686, h2887, h2900, h2904, h2962, h2964, hc46, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b]
                                                          · linarith only [h2681, h2806, h2889, h2903, h2963, hc05, hlam, hphi, ht56, u6elo0]
                                                        · linarith only [h2678, h2686, h2887, h2900, h2962, hc36, hlam, hphi, u6elo4]
                                                    · linarith only [h0, h2680, h2895, h2903, hc12, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                                · linarith only [h2900, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h2895, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h2894, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h2889, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h2683, h2888, hlam]
                              · linarith only [h0, h2682, h2887, hlam]
                            · linarith only [h2847, h2886, hc04, hlam, hphi, ht45, ht56, u6elo5]
                          · linarith only [h2686, h2846, h2885, hc36, hlam, hphi, u6elo4]
                      · linarith only [h2846, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h2685, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · linarith only [h0, h2680, h2684, hlam]
            · linarith only [h0, h2679, h2683, hlam]
          · linarith only [h0, h2678, h2682, hlam]
        · linarith only [h2681, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h3040 | h3040
        · rcases m.htr 0 2 3 (by decide) (by decide) with h3041 | h3041
          · rcases m.htr 0 2 4 (by decide) (by decide) with h3042 | h3042
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3043 | h3043
              · rcases m.htr 0 2 6 (by decide) (by decide) with h3044 | h3044
                · rcases m.htr 0 3 4 (by decide) (by decide) with h3045 | h3045
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3046 | h3046
                    · linarith only [h2678, h2680, h3046, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3048 | h3048
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3049 | h3049
                        · linarith only [h2678, h2680, h3045, h3049, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3051 | h3051
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3052 | h3052
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3053 | h3053
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3054 | h3054
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3055 | h3055
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3056 | h3056
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3057 | h3057
                                      · linarith only [h2678, h3046, h3057, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3059 | h3059
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h3060 | h3060
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3061 | h3061
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3062 | h3062
                                              · linarith only [h2678, h2680, h3053, h3057, h3062, hlam]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h3064 | h3064
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3065 | h3065
                                                  · linarith only [h2678, h2680, h3049, h3054, h3056, h3057, h3065, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h3067 | h3067
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3068 | h3068
                                                      · linarith only [h2678, h2680, h3049, h3053, h3057, h3061, h3068, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                                      · linarith only [h2678, h2680, h3053, h3057, h3061, h3068, hc34, hc45, hlam, hphi]
                                                    · linarith only [h3067, hc25, hlam, hphi, ht56, u6elo5]
                                                · linarith only [h3061, h3064, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                            · linarith only [h2678, h2680, h3045, h3057, h3061, hc23, hc35, hlam, hphi]
                                          · linarith only [h2678, h2680, h3056, h3060, hc34, hc56, hlam, hphi, ht45]
                                        · linarith only [h3056, h3059, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                    · linarith only [h3045, h3046, h3056, hc13, hc35, hlam, hphi]
                                  · linarith only [h0, h3055, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h3042, h3054, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                              · linarith only [h0, h2678, h3041, h3045, h3053, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h3052, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h3051, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h3045, h3048, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3083 | h3083
                    · linarith only [h2679, h2680, h3045, h3083, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3085 | h3085
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3086 | h3086
                        · linarith only [h2679, h2680, h3086, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3088 | h3088
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3089 | h3089
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3090 | h3090
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3091 | h3091
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3092 | h3092
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3093 | h3093
                                    · linarith only [h2678, h3045, h3093, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3095 | h3095
                                      · linarith only [h2678, h2680, h3083, h3095, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3097 | h3097
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h3098 | h3098
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3099 | h3099
                                            · linarith only [h3041, h3045, h3099, hlam]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3101 | h3101
                                              · linarith only [h2680, h3041, h3095, h3101, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h3103 | h3103
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3104 | h3104
                                                  · linarith only [h2678, h2679, h3045, h3086, h3090, h3091, h3103, h3104, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h3106 | h3106
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3107 | h3107
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h3108 | h3108
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h3109 | h3109
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h3110 | h3110
                                                            · rcases h0bigk with h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c | h3111c
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h0, hlam, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2678, h2680, h3086, h3090, h3103, h3107, h3108, h3110, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2678, h2680, h3045, h3086, h3090, h3103, h3107, h3108, h3110, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2680, hlam, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                rcases p3111_3 (m.d 0 1) (by simp) with h3117 | h3117
                                                                · rcases p3111_3 (m.d 0 2) (by simp) with h3118 | h3118
                                                                  · rcases p3111_3 (m.d 0 3) (by simp) with h3119 | h3119
                                                                    · linarith only [h2678, h3119, hlam]
                                                                    · linarith only [h3085, h3119, hlam]
                                                                  · linarith only [h3044, h3118, hlam]
                                                                · linarith only [h3040, h3117, hlam]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2678, h3090, h3103, h3108, h3110, hc56, hlam, hphi, ht0b, ht6b, p3111_1, u0elo1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2678, h3090, h3103, h3108, h3110, hc56, hlam, hphi, ht0b, ht6b, p3111_1, u0elo1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2678, h3045, h3090, h3103, h3108, h3110, hc56, hlam, hphi, ht0b, ht6b, p3111_1, u0elo1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2679, h2680, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p3111_1, u0elo1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                rcases p3111_3 (m.d 0 1) (by simp) with h3129 | h3129
                                                                · linarith only [h0, h3129, hlam]
                                                                · linarith only [h3040, h3129, hlam]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2678, hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3041, hlam, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3045, hlam, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3083, hlam, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3040, h3045, h3086, h3092, h3103, h3107, h3108, h3110, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2679, hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3042, hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2678, h2679, h2680, h3090, h3103, h3108, h3110, hc56, hlam, hphi, ht0b, ht6b, p3111_1, u0elo4]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3086, hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3040, h3086, h3092, h3103, h3107, h3108, h3110, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3086, h3107, hc01, hc34, hlam, hphi, ht12, ht23, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3043, hlam, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2678, h3086, h3090, h3103, h3107, h3108, h3110, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h2679, h3086, h3090, h3093, h3103, h3107, h3108, h3110, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p3111_1]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                rcases p3111_3 (m.d 0 1) (by simp) with h3149 | h3149
                                                                · linarith only [h2680, h3149, hlam]
                                                                · linarith only [h3040, h3149, hlam]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3040, hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3044, hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3085, hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3088, hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [h3089, hlam, p3111_0]
                                                              · obtain ⟨p3111_0, p3111_1, p3111_2, p3111_3⟩ := h3111c
                                                                linarith only [hlam, p3111_0]
                                                            · linarith only [h3086, h3110, hc05, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h2679, h2680, h3040, h3092, h3093, h3095, h3106, h3109, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo5]
                                                        · linarith only [h2679, h2680, h3090, h3093, h3095, h3103, h3107, h3108, hc36, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h3161 | h3161
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h3162 | h3162
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h3163 | h3163
                                                            · rcases h0bigk with h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h0, hlam, p3164_1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2678, h3090, h3103, h3161, h3163, hc56, hlam, hphi, ht0b, ht6b, p3164_1, u0elo0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2678, h2680, h3045, h3090, h3095, h3103, h3161, h3163, hc35, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p3164_1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2680, hlam, p3164_1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                rcases p3164_3 (m.d 0 1) (by simp) with h3170 | h3170
                                                                · rcases p3164_3 (m.d 0 2) (by simp) with h3171 | h3171
                                                                  · rcases p3164_3 (m.d 0 3) (by simp) with h3172 | h3172
                                                                    · linarith only [h2678, h3172, hlam]
                                                                    · linarith only [h3085, h3172, hlam]
                                                                  · linarith only [h3044, h3171, hlam]
                                                                · linarith only [h3040, h3170, hlam]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2678, h3090, h3103, h3161, h3163, hc56, hlam, hphi, ht0b, ht6b, p3164_1, u0elo1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2678, h3090, h3103, h3161, h3163, hc56, hlam, hphi, ht0b, ht6b, p3164_1, u0elo1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2678, h3045, h3090, h3103, h3161, h3163, hc56, hlam, hphi, ht0b, ht6b, p3164_1, u0elo1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2679, h2680, h3090, h3093, h3103, h3161, h3163, hc56, hlam, hphi, ht0b, ht6b, p3164_1, u0elo1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                rcases p3164_3 (m.d 0 1) (by simp) with h3182 | h3182
                                                                · linarith only [h0, h3182, hlam]
                                                                · linarith only [h3040, h3182, hlam]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2678, hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3041, hlam, p3164_1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3045, hlam, p3164_1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3083, hlam, p3164_1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3040, h3045, h3092, h3103, h3107, h3161, h3163, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p3164_1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2679, hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3042, hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2678, h2679, h2680, h3090, h3103, h3161, h3163, hc56, hlam, hphi, ht0b, ht6b, p3164_1, u0elo4]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3086, hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                rcases p3164_3 (m.d 0 1) (by simp) with h3196 | h3196
                                                                · rcases p3164_3 (m.d 0 2) (by simp) with h3197 | h3197
                                                                  · rcases p3164_3 (m.d 0 3) (by simp) with h3198 | h3198
                                                                    · linarith only [h3045, h3198, hlam]
                                                                    · linarith only [h3085, h3198, hlam]
                                                                  · linarith only [h3044, h3197, hlam]
                                                                · linarith only [h3040, h3196, hlam]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2678, h3043, h3090, h3103, h3161, h3163, hc56, hlam, hphi, ht0b, ht6b, p3164_1, u0elo1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3043, hlam, p3164_1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2678, h3043, h3090, h3103, h3161, h3163, hc56, hlam, hphi, ht0b, ht6b, p3164_1, u0elo1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h2679, h3043, h3090, h3093, h3103, h3161, h3163, hc56, hlam, hphi, ht0b, ht6b, p3164_1, u0elo1]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                rcases p3164_3 (m.d 0 1) (by simp) with h3208 | h3208
                                                                · linarith only [h2680, h3208, hlam]
                                                                · linarith only [h3040, h3208, hlam]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3040, hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3044, hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3085, hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3088, hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [h3089, hlam, p3164_0]
                                                              · obtain ⟨p3164_0, p3164_1, p3164_2, p3164_3⟩ := h3164c
                                                                linarith only [hlam, p3164_0]
                                                            · linarith only [h3107, h3163, hc34, hlam, hphi, ht45, ht56, u6elo5]
                                                          · linarith only [h2679, h2680, h3040, h3092, h3093, h3095, h3106, h3162, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo5]
                                                        · linarith only [h2678, h3045, h3090, h3103, h3161, hc36, hlam, hphi, u6elo4]
                                                    · linarith only [h3099, h3103, h3104, h3106, hc36, hlam, hphi, u6elo5]
                                                · linarith only [h3103, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h2679, h2680, h3093, h3098, hc13, hc56, hlam, hphi, ht34, ht45]
                                        · linarith only [h3045, h3085, h3090, h3097, hc23, hc34, hlam, hphi]
                                  · linarith only [h3092, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h3042, h3091, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                              · linarith only [h0, h3041, h3090, hlam]
                            · linarith only [h2680, h3089, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h3045, h3088, hc03, hlam, hphi, ht34, ht45, ht56, u6elo4]
                      · linarith only [h3041, h3085, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h3044, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h3231 | h3231
                · rcases m.htr 0 3 4 (by decide) (by decide) with h3232 | h3232
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3233 | h3233
                    · linarith only [h0, h2678, h3043, h3233, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3235 | h3235
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3236 | h3236
                        · linarith only [h0, h2679, h3043, h3236, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3238 | h3238
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3239 | h3239
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3240 | h3240
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3241 | h3241
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3242 | h3242
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3243 | h3243
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3244 | h3244
                                      · linarith only [h2678, h3233, h3244, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3246 | h3246
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h3247 | h3247
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3248 | h3248
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3249 | h3249
                                              · linarith only [h2678, h2680, h3240, h3244, h3249, hlam]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h3251 | h3251
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3252 | h3252
                                                  · linarith only [h0, h2679, h3043, h3236, h3241, h3249, h3252, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                                  · linarith only [h0, h2678, h3043, h3243, h3252, hc34, hc45, hlam, hphi]
                                                · linarith only [h3248, h3251, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                            · linarith only [h3232, h3233, h3248, hc23, hc35, hlam, hphi]
                                          · linarith only [h2678, h2680, h3247, hc13, hc56, hlam, hphi, ht34, ht45]
                                        · linarith only [h3243, h3246, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                    · linarith only [h3232, h3233, h3240, h3243, hc23, hc35, hlam, hphi]
                                  · linarith only [h0, h3242, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h3042, h3241, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                              · linarith only [h0, h3041, h3240, hlam]
                            · linarith only [h3239, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h3238, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h3232, h3235, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3266 | h3266
                    · linarith only [h0, h2679, h3043, h3232, h3266, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3268 | h3268
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3269 | h3269
                        · linarith only [h0, h2679, h3043, h3269, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3271 | h3271
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3272 | h3272
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3273 | h3273
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3274 | h3274
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3275 | h3275
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3276 | h3276
                                    · linarith only [h0, h2678, h3232, h3276, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3278 | h3278
                                      · linarith only [h2678, h2680, h3266, h3278, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3280 | h3280
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h3281 | h3281
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3282 | h3282
                                            · linarith only [h3041, h3232, h3282, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3284 | h3284
                                              · linarith only [h2678, h2680, h3278, h3280, h3282, h3284, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h3286 | h3286
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3287 | h3287
                                                  · linarith only [h2679, h2680, h3269, h3274, h3287, hlam]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h3289 | h3289
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3290 | h3290
                                                      · linarith only [h0, h2678, h3043, h3273, h3286, h3287, h3290, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h3292 | h3292
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h3293 | h3293
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h3294 | h3294
                                                            · rcases h0bigk with h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h0, hlam, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2678, h3273, h3286, h3292, h3294, hc56, hlam, hphi, ht0b, ht6b, p3295_1, u0elo0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h0, h2679, h3043, h3273, h3276, h3286, h3292, h3294, hc25, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2680, hlam, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                rcases p3295_3 (m.d 0 1) (by simp) with h3301 | h3301
                                                                · rcases p3295_3 (m.d 0 2) (by simp) with h3302 | h3302
                                                                  · rcases p3295_3 (m.d 0 3) (by simp) with h3303 | h3303
                                                                    · linarith only [h2678, h3303, hlam]
                                                                    · linarith only [h3268, h3303, hlam]
                                                                  · linarith only [h3231, h3302, hlam]
                                                                · linarith only [h3040, h3301, hlam]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3043, h3284, h3290, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2678, h3043, h3273, h3284, h3286, h3290, h3292, h3294, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2679, h3043, h3273, h3276, h3284, h3286, h3290, h3292, h3294, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3043, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                rcases p3295_3 (m.d 0 1) (by simp) with h3313 | h3313
                                                                · linarith only [h0, h3313, hlam]
                                                                · linarith only [h3040, h3313, hlam]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2678, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3041, hlam, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3232, hlam, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3266, hlam, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3040, h3232, h3275, h3286, h3290, h3292, h3294, hc45, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p3295_1]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2679, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3042, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2678, h3273, h3286, h3292, h3294, hc56, hlam, hphi, ht0b, ht6b, p3295_1, u0elo3]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3269, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                rcases p3295_3 (m.d 0 1) (by simp) with h3327 | h3327
                                                                · rcases p3295_3 (m.d 0 2) (by simp) with h3328 | h3328
                                                                  · rcases p3295_3 (m.d 0 3) (by simp) with h3329 | h3329
                                                                    · linarith only [h3232, h3329, hlam]
                                                                    · linarith only [h3268, h3329, hlam]
                                                                  · linarith only [h3231, h3328, hlam]
                                                                · linarith only [h3040, h3327, hlam]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2678, h3273, h3286, h3292, h3294, hc56, hlam, hphi, ht0b, ht6b, p3295_1, u0elo4]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h0, h2679, h3273, h3276, h3286, h3292, h3294, hc56, hlam, hphi, ht0b, ht6b, p3295_1, u0elo4]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2678, h3273, h3286, h3292, h3294, hc56, hlam, hphi, ht0b, ht6b, p3295_1, u0elo4]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h2679, h3273, h3276, h3286, h3292, h3294, hc56, hlam, hphi, ht0b, ht6b, p3295_1, u0elo4]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                rcases p3295_3 (m.d 0 1) (by simp) with h3339 | h3339
                                                                · linarith only [h2680, h3339, hlam]
                                                                · linarith only [h3040, h3339, hlam]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3040, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3231, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3268, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3271, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [h3272, hlam, p3295_0]
                                                              · obtain ⟨p3295_0, p3295_1, p3295_2, p3295_3⟩ := h3295c
                                                                linarith only [hlam, p3295_0]
                                                            · linarith only [h3290, h3294, hc34, hlam, hphi, ht45, ht56, u6elo5]
                                                          · linarith only [h0, h2679, h3040, h3043, h3275, h3276, h3284, h3289, h3293, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo5]
                                                        · linarith only [h2678, h3232, h3273, h3286, h3292, hc36, hlam, hphi, u6elo4]
                                                    · linarith only [h0, h2679, h3043, h3273, h3276, h3286, h3289, hc36, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b]
                                                · linarith only [h3286, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h3281, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h3280, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h2678, h3231, h3273, h3275, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                · linarith only [h0, h3042, h3274, hlam]
                              · linarith only [h0, h3041, h3273, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h3272, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h3232, h3271, hc03, hlam, hphi, ht34, ht45, ht56, u6elo4]
                      · linarith only [h3041, h3268, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h3231, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · linarith only [h0, h2679, h3042, hlam]
          · linarith only [h0, h2678, h3041, hlam]
        · linarith only [h2678, h3040, hc13, hlam, hphi, ht34, ht45, ht56, u6elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3365 | h3365
      · rcases m.htr 0 1 6 (by decide) (by decide) with h3366 | h3366
        · rcases m.htr 0 2 3 (by decide) (by decide) with h3367 | h3367
          · rcases m.htr 0 2 4 (by decide) (by decide) with h3368 | h3368
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3369 | h3369
              · rcases m.htr 0 2 6 (by decide) (by decide) with h3370 | h3370
                · rcases m.htr 0 3 4 (by decide) (by decide) with h3371 | h3371
                  · linarith only [h2678, h2679, h3371, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3373 | h3373
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3374 | h3374
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3375 | h3375
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3376 | h3376
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3377 | h3377
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3378 | h3378
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3379 | h3379
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3380 | h3380
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3381 | h3381
                                    · linarith only [h2678, h3371, h3381, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3383 | h3383
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3384 | h3384
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h3385 | h3385
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3386 | h3386
                                            · linarith only [h2678, h2679, h3378, h3381, h3386, hlam]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3388 | h3388
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h3389 | h3389
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3390 | h3390
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h3391 | h3391
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3392 | h3392
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h3393 | h3393
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h3394 | h3394
                                                          · linarith only [h2678, h2679, h3378, h3381, h3388, h3394, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                          · linarith only [h3392, h3394, hc45, hlam, hphi, ht56, u6elo5]
                                                        · linarith only [h2678, h2679, h3378, h3381, h3388, h3392, h3393, hc45, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b]
                                                      · linarith only [h2678, h2679, h3378, h3381, h3388, h3392, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b]
                                                    · linarith only [h3391, hc25, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h3368, h3375, h3386, h3388, h3390, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                                · linarith only [h3388, h3389, hc35, hlam, hphi, ht56, u6elo3]
                                              · linarith only [h2678, h2679, h3373, h3381, h3388, hc23, hc34, hlam, hphi]
                                          · linarith only [h3385, hc15, hlam, hphi, ht56, u6elo5]
                                        · linarith only [h3384, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                      · linarith only [h2678, h2679, h3373, h3378, h3381, h3383, hc23, hc34, hlam, hphi]
                                  · linarith only [h3380, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h3368, h3379, hlam]
                              · linarith only [h0, h3367, h3378, hlam]
                            · linarith only [h3377, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h3376, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h2679, h3365, h3375, hlam]
                      · linarith only [h3374, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3413 | h3413
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3414 | h3414
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3415 | h3415
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3416 | h3416
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3417 | h3417
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3418 | h3418
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3419 | h3419
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3420 | h3420
                                    · linarith only [h2678, h2679, h3371, h3413, h3418, h3420, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3422 | h3422
                                      · linarith only [h2678, h3373, h3422, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3424 | h3424
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h3425 | h3425
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3426 | h3426
                                            · linarith only [h2678, h2679, h3420, h3424, h3426, hc23, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3428 | h3428
                                              · linarith only [h2678, h3373, h3417, h3428, hlam]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h3430 | h3430
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3431 | h3431
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h3432 | h3432
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3433 | h3433
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h3434 | h3434
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h3435 | h3435
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h3436 | h3436
                                                            · linarith only [h3368, h3431, h3436, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                                                            · linarith only [h3436, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h2678, h3373, h3417, h3430, h3432, h3434, h3435, hc25, hc46, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                        · linarith only [h2679, h3365, h3420, h3422, h3434, hc13, hc46, hlam, hphi, ht34]
                                                      · linarith only [h2679, h3365, h3417, h3420, h3422, h3430, h3433, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h3432, hc25, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h3368, h3414, h3426, h3430, h3431, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                · linarith only [h3430, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h3422, h3425, hc13, hlam, hphi, ht34, ht45, ht56, u6elo5]
                                        · linarith only [h3373, h3413, h3417, h3424, hc23, hc35, hlam, hphi]
                                  · linarith only [h3419, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h3368, h3418, hlam]
                              · linarith only [h0, h3367, h3417, hlam]
                            · linarith only [h3373, h3416, hc03, hlam, hphi, ht34, ht45, ht56, u6elo5]
                          · linarith only [h3415, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h2679, h3365, h3414, hlam]
                      · linarith only [h3413, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h3370, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · linarith only [h2679, h3365, h3368, h3369, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3456 | h3456
              · rcases m.htr 0 2 6 (by decide) (by decide) with h3457 | h3457
                · rcases m.htr 0 3 4 (by decide) (by decide) with h3458 | h3458
                  · linarith only [h0, h2678, h3368, h3458, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3460 | h3460
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3461 | h3461
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3462 | h3462
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3463 | h3463
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3464 | h3464
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3465 | h3465
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3466 | h3466
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3467 | h3467
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3468 | h3468
                                    · linarith only [h0, h2678, h3458, h3468, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3470 | h3470
                                      · linarith only [h0, h2678, h3368, h3466, h3470, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                      · linarith only [h0, h2678, h3368, h3460, h3466, h3470, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                  · linarith only [h0, h3368, h3466, h3467, hc01, hc26, hlam, hphi, ht12]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3474 | h3474
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3475 | h3475
                                    · linarith only [h0, h2678, h3458, h3466, h3475, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3477 | h3477
                                      · linarith only [h0, h2678, h3466, h3477, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                      · linarith only [h0, h2678, h3460, h3466, h3477, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                                  · linarith only [h0, h3474, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h2678, h3367, h3465, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h3365, h3464, hc15, hlam, hphi, ht56, u6elo5]
                          · linarith only [h3463, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h0, h3365, h3368, h3462, hlam]
                      · linarith only [h3461, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3486 | h3486
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3487 | h3487
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3488 | h3488
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3489 | h3489
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3490 | h3490
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3491 | h3491
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3492 | h3492
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3493 | h3493
                                    · linarith only [h0, h2678, h3368, h3458, h3486, h3491, h3493, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3495 | h3495
                                      · linarith only [h0, h2678, h3368, h3460, h3486, h3491, h3495, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3497 | h3497
                                        · linarith only [h0, h3365, h3368, h3491, h3495, h3497, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h3460, h3486, h3490, h3497, hc23, hc35, hlam, hphi]
                                  · linarith only [h0, h3368, h3491, h3492, hc01, hc26, hlam, hphi, ht12]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3501 | h3501
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3502 | h3502
                                    · linarith only [h0, h2678, h3491, h3502, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3504 | h3504
                                      · linarith only [h0, h2678, h3460, h3491, h3504, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3506 | h3506
                                        · linarith only [h0, h3365, h3491, h3504, h3506, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h3460, h3486, h3490, h3506, hc23, hc35, hlam, hphi]
                                  · linarith only [h0, h3501, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3367, h3490, hlam]
                            · linarith only [h3460, h3486, h3489, hc36, hlam, hphi, u6elo5]
                          · linarith only [h3488, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h0, h3365, h3368, h3487, hlam]
                      · linarith only [h3486, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h0, h3457, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
              · linarith only [h0, h3365, h3456, hlam]
          · linarith only [h0, h2678, h3367, hlam]
        · linarith only [h2678, h3366, hc13, hlam, hphi, ht34, ht45, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h3519 | h3519
        · rcases m.htr 0 2 3 (by decide) (by decide) with h3520 | h3520
          · rcases m.htr 0 2 4 (by decide) (by decide) with h3521 | h3521
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3522 | h3522
              · rcases m.htr 0 2 6 (by decide) (by decide) with h3523 | h3523
                · rcases m.htr 0 3 4 (by decide) (by decide) with h3524 | h3524
                  · linarith only [h2678, h2679, h3524, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3526 | h3526
                    · linarith only [h2678, h3365, h3526, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3528 | h3528
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3529 | h3529
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3530 | h3530
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3531 | h3531
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3532 | h3532
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3533 | h3533
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3534 | h3534
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3535 | h3535
                                    · linarith only [h2678, h3524, h3535, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3537 | h3537
                                      · linarith only [h2678, h3365, h3526, h3537, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3539 | h3539
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h3540 | h3540
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3541 | h3541
                                            · linarith only [h2678, h2679, h3532, h3535, h3541, hlam]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3543 | h3543
                                              · linarith only [h2678, h3365, h3532, h3537, h3543, hlam]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h3545 | h3545
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3546 | h3546
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h3547 | h3547
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3548 | h3548
                                                      · rcases m.htr 3 4 6 (by decide) (by decide) with h3549 | h3549
                                                        · rcases m.htr 3 5 6 (by decide) (by decide) with h3550 | h3550
                                                          · rcases m.htr 4 5 6 (by decide) (by decide) with h3551 | h3551
                                                            · linarith only [h3521, h3546, h3551, hc56, hlam, hphi, ht0b, ht6b, u0elo1]
                                                            · linarith only [h3551, hc45, hlam, hphi, ht56, u6elo5]
                                                          · linarith only [h3365, h3519, h3534, h3537, h3547, h3550, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo0]
                                                        · linarith only [h2678, h3365, h3532, h3537, h3545, h3548, h3549, hc36, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                      · linarith only [h2678, h2679, h3532, h3535, h3545, h3548, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h3547, hc25, hlam, hphi, ht56, u6elo5]
                                                  · linarith only [h3521, h3529, h3541, h3545, h3546, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                · linarith only [h3545, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h2678, h3365, h3540, hc13, hc56, hlam, hphi, ht34, ht45]
                                        · linarith only [h3532, h3539, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h3534, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h3521, h3533, hlam]
                              · linarith only [h0, h3520, h3532, hlam]
                            · linarith only [h3531, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h3530, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3567 | h3567
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3568 | h3568
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3569 | h3569
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3570 | h3570
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3571 | h3571
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3572 | h3572
                                    · linarith only [h2678, h2679, h3529, h3572, hc34, hc45, hlam, hphi]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3574 | h3574
                                      · linarith only [h2678, h3526, h3574, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3576 | h3576
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h3577 | h3577
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3578 | h3578
                                            · linarith only [h2678, h2679, h3569, h3572, h3578, hlam]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3580 | h3580
                                              · linarith only [h2678, h3365, h3569, h3574, h3580, hlam]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h3582 | h3582
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3583 | h3583
                                                  · linarith only [h2678, h2679, h3521, h3529, h3569, h3582, h3583, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h3585 | h3585
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3586 | h3586
                                                      · linarith only [h2678, h2679, h3529, h3569, h3582, h3586, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                      · linarith only [h2678, h2679, h3569, h3572, h3582, h3586, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h3583, h3585, hc24, hlam, hphi, ht45, ht56, u6elo5]
                                                · linarith only [h3582, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h2678, h3365, h3577, hc13, hc56, hlam, hphi, ht34, ht45]
                                        · linarith only [h3569, h3576, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h3571, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h2678, h3521, h3569, h3570, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                              · linarith only [h0, h3520, h3569, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h3529, h3568, hc04, hlam, hphi, ht45, ht56, u6elo5]
                          · linarith only [h2678, h2679, h3567, hc13, hlam, hphi, ht34, ht45, ht56, u6elo4]
                      · linarith only [h3528, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h3523, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h3600 | h3600
                · rcases m.htr 0 3 4 (by decide) (by decide) with h3601 | h3601
                  · linarith only [h2678, h2679, h3601, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3603 | h3603
                    · linarith only [h2678, h2679, h3521, h3522, h3603, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3605 | h3605
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3606 | h3606
                        · linarith only [h3521, h3522, h3606, hlam]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3608 | h3608
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3609 | h3609
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3610 | h3610
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3611 | h3611
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3612 | h3612
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3613 | h3613
                                    · linarith only [h2678, h3601, h3613, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3615 | h3615
                                      · linarith only [h2678, h3365, h3603, h3615, hlam]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3617 | h3617
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h3618 | h3618
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3619 | h3619
                                            · linarith only [h2678, h2679, h3610, h3613, h3619, hlam]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3621 | h3621
                                              · linarith only [h2678, h3365, h3610, h3615, h3621, hlam]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h3623 | h3623
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3624 | h3624
                                                  · linarith only [h2678, h2679, h3606, h3610, h3623, h3624, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h3626 | h3626
                                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3627 | h3627
                                                      · linarith only [h0, h2678, h3522, h3610, h3623, h3624, h3627, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                                      · linarith only [h2678, h2679, h3610, h3613, h3623, h3627, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                                    · linarith only [h2678, h2679, h3521, h3522, h3610, h3623, h3626, hc36, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b]
                                                · linarith only [h3623, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                          · linarith only [h2678, h3365, h3618, hc13, hc56, hlam, hphi, ht34, ht45]
                                        · linarith only [h3610, h3617, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h2678, h2679, h3610, h3611, h3612, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                                · linarith only [h0, h3521, h3611, hlam]
                              · linarith only [h0, h3520, h3610, hlam]
                            · linarith only [h3609, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h3608, hc04, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h3605, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h3600, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h3641 | h3641
              · rcases m.htr 0 2 6 (by decide) (by decide) with h3642 | h3642
                · rcases m.htr 0 3 4 (by decide) (by decide) with h3643 | h3643
                  · linarith only [h2678, h3365, h3521, h3641, h3643, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3645 | h3645
                    · linarith only [h2678, h3365, h3645, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3647 | h3647
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3648 | h3648
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3649 | h3649
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3650 | h3650
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3651 | h3651
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3652 | h3652
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3653 | h3653
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3654 | h3654
                                    · linarith only [h2678, h3643, h3654, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3656 | h3656
                                      · linarith only [h2678, h3365, h3521, h3641, h3645, h3647, h3652, h3656, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3658 | h3658
                                        · linarith only [h2678, h3365, h3521, h3641, h3652, h3658, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h3651, h3658, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h3365, h3521, h3641, h3652, h3653, hc01, hc26, hlam, hphi, ht12]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3662 | h3662
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3663 | h3663
                                    · linarith only [h0, h2678, h3643, h3652, h3663, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3665 | h3665
                                      · linarith only [h0, h2678, h3652, h3665, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3667 | h3667
                                        · linarith only [h0, h2678, h3652, h3667, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h3651, h3667, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h2678, h3651, h3662, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3520, h3651, hlam]
                            · linarith only [h3650, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h3521, h3649, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                        · linarith only [h3521, h3641, h3648, hlam]
                      · linarith only [h3647, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h3642, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 0 2 6 (by decide) (by decide) with h3677 | h3677
                · rcases m.htr 0 3 4 (by decide) (by decide) with h3678 | h3678
                  · linarith only [h0, h2678, h3521, h3678, hlam]
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h3680 | h3680
                    · linarith only [h0, h2678, h3641, h3680, hlam]
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3682 | h3682
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h3683 | h3683
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3684 | h3684
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3685 | h3685
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3686 | h3686
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3687 | h3687
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3688 | h3688
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3689 | h3689
                                    · linarith only [h0, h2678, h3521, h3678, h3687, h3689, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3691 | h3691
                                      · linarith only [h0, h2678, h3521, h3680, h3682, h3687, h3691, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3693 | h3693
                                        · linarith only [h0, h2678, h3521, h3687, h3693, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h3686, h3693, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h3521, h3687, h3688, hc01, hc26, hlam, hphi, ht12]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3697 | h3697
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3698 | h3698
                                    · linarith only [h0, h2678, h3687, h3698, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3700 | h3700
                                      · linarith only [h0, h2678, h3687, h3700, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3702 | h3702
                                        · linarith only [h0, h2678, h3687, h3702, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h3702, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h3697, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h3520, h3686, hlam]
                            · linarith only [h3685, hc05, hlam, hphi, ht56, u6elo5]
                          · linarith only [h3684, hc04, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h3709 | h3709
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h3710 | h3710
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h3711 | h3711
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h3712 | h3712
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3713 | h3713
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3714 | h3714
                                    · linarith only [h0, h2678, h3521, h3712, h3714, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3716 | h3716
                                      · linarith only [h0, h2678, h3521, h3712, h3716, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3718 | h3718
                                        · linarith only [h0, h2678, h3521, h3712, h3718, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                        · linarith only [h3718, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h3521, h3712, h3713, hc01, hc26, hlam, hphi, ht12]
                                · rcases m.htr 1 2 6 (by decide) (by decide) with h3722 | h3722
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3723 | h3723
                                    · linarith only [h0, h2678, h3712, h3723, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3725 | h3725
                                      · linarith only [h0, h2678, h3712, h3725, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                                      · rcases m.htr 1 3 6 (by decide) (by decide) with h3727 | h3727
                                        · linarith only [h0, h2678, h3712, h3727, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                        · linarith only [h3711, h3727, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                                  · linarith only [h0, h3722, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h2678, h3520, h3521, h3683, h3711, hc13, hc45, hlam, hphi, ht34]
                            · linarith only [h3521, h3683, h3710, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h0, h2678, h3521, h3709, hc13, hlam, hphi, ht34, ht45, ht56, u6elo4]
                      · linarith only [h3682, hc03, hlam, hphi, ht34, ht45, ht56, u6elo3]
                · linarith only [h0, h2678, h3677, hc13, hlam, hphi, ht34, ht45, ht56, u6elo2]
          · linarith only [h0, h2678, h3520, hlam]
        · linarith only [h2678, h3519, hc13, hlam, hphi, ht34, ht45, ht56, u6elo1]
  · exact n8l_sBT8_M_LI_H_L_s2 m hb0 hb6 h0 h2678

set_option maxHeartbeats 13274000 in
theorem n8l_sBT8_M_LI_H_L (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h6elo := hb6.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0elo5 := h0elo (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact n8l_sBT8_M_LI_H_L_s0 m hb0 hb6 h0
  · exact n8l_sBT8_M_LI_H_L_s1 m hb0 hb6 h0

end R2N4
