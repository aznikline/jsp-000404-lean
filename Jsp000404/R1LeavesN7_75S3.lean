import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_25_L_R_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h11, h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h0, h10, h11, h13, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                            · linarith only [h11, h16, h6, h8, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h0, h15, h16, h2, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h10, h11, h15, h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h10, h20, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h0, h10, h2, h22, h3, h7, h8, hc01, hc25, hlam, hphi, ht0b, ht12, ht5b, u1ehi2, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                          · linarith only [h10, h24, hc23, hlam, hphi, ht12, u1ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                            · linarith only [h20, h24, h26, h7, h8, hc25, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                              · linarith only [h0, h2, h26, h28, h4, h7, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                                · linarith only [h24, h28, h30, h7, h8, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h10, h2, h3, h30, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                  · linarith only [h33, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                    · linarith only [h35, h6, h7, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                      · linarith only [h0, h2, h3, h35, h37, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                        · linarith only [h0, h2, h3, h35, h39, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                          · linarith only [h0, h2, h3, h39, h41, h5, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                            · linarith only [h0, h2, h3, h37, h39, h43, h5, h6, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                              · linarith only [h39, h41, h45, h6, h7, hc23, hc34, hlam, hphi]
                              · linarith only [h0, h2, h3, h45, h5, h6, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                  · linarith only [h49, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                      · linarith only [h0, h2, h52, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                        · linarith only [h0, h2, h4, h48, h52, h54, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                            · linarith only [h0, h2, h48, h52, h57, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                            · linarith only [h4, h48, h57, h6, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                          · linarith only [h48, h56, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · linarith only [h48, h51, h6, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h62 | h62
                  · linarith only [h6, h62, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h0, h2, h6, h65, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                        · linarith only [h0, h2, h4, h64, h65, h67, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                            · linarith only [h0, h2, h48, h64, h65, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h4, h6, h70, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                          · linarith only [h6, h64, h69, hc13, hlam, hphi, u1ehi1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                      · linarith only [h0, h2, h3, h64, h74, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                        · linarith only [h0, h2, h3, h64, h76, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                          · linarith only [h0, h2, h64, h78, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                          · linarith only [h0, h2, h3, h6, h78, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
              · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                  · linarith only [h0, h83, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                      · linarith only [h81, h83, h86, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h88 | h88
                        · linarith only [h0, h2, h4, h5, h85, h86, h88, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                            · linarith only [h81, h83, h86, h91, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h0, h2, h4, h81, h83, h90, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h2, h4, h85, h86, h90, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h3, h5, h85, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                  · linarith only [h82, h96, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                    · linarith only [h81, h82, h98, hlam]
                    · linarith only [h3, h5, h98, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                  · linarith only [h0, h102, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                      · linarith only [h0, h105, h2, h81, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                        · linarith only [h0, h101, h105, h107, h2, h4, h5, h81, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                            · linarith only [h101, h105, h110, h81, hc23, hlam, hphi, ht12, u1ehi3]
                            · linarith only [h0, h101, h110, h2, h4, h81, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                          · linarith only [h101, h109, h81, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · linarith only [h101, h104, h3, h5, h81, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                  · linarith only [h115, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                      · linarith only [h1, h118, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                        · linarith only [h0, h117, h118, h120, h2, h4, h5, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                            · linarith only [h0, h101, h117, h118, h123, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h123, h4, h81, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                          · linarith only [h117, h122, h81, hc13, hlam, hphi, u1ehi1]
                    · linarith only [h117, h3, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
            · linarith only [h128, h3, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
              · rcases m.htr 1 2 4 (by decide) (by decide) with h131 | h131
                · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                  · linarith only [h0, h132, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                      · linarith only [h1, h135, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                        · linarith only [h128, h131, h132, h137, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h139 | h139
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                            · linarith only [h130, h132, h140, h4, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                              · linarith only [h130, h132, h137, h139, h140, h142, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h130, h132, h139, h142, hc34, hc45, hlam, hphi]
                          · linarith only [h139, h3, h4, hc23, hc35, hlam, hphi]
                    · linarith only [h134, h3, h4, hc13, hc35, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                  · linarith only [h131, h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                    · linarith only [h130, h131, h149, hlam]
                    · linarith only [h149, h3, h4, hc13, hc35, hlam, hphi]
              · linarith only [h130, h2, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h153 | h153
          · linarith only [h153, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
            · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
              · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                · rcases m.htr 1 2 5 (by decide) (by decide) with h158 | h158
                  · linarith only [h0, h158, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                    · linarith only [h1, h160, h3, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                      · linarith only [h1, h153, h162, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                        · linarith only [h157, h158, h164, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h155, h164, h3, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                  · linarith only [h157, h167, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
                    · linarith only [h1, h155, h169, h3, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                      · linarith only [h1, h153, h171, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                          · linarith only [h156, h157, h174, h3, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                            · linarith only [h1, h153, h156, h157, h174, h176, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h179 | h179
                                · rcases h3bigk with h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h3, hc34, hlam, hphi, ht12, ht23, p180_1, u1ehi2]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h3, hc23, hc34, hlam, hphi, p180_1]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h3, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h153, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h1, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h1, h3, hc23, hc34, hlam, hphi, p180_1]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h169, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h171, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h2, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h156, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h174, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h176, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht12, ht23, p180_1, u1ehi2]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hc34, hlam, hphi, ht12, ht23, p180_1, u1ehi2]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    rcases p180_3 (m.d 0 3) (by simp) with h198 | h198
                                    · linarith only [h198, h3, hlam]
                                    · linarith only [h198, h2, hlam]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h167, h176, hc12, hc34, hlam, hphi, ht23, p180_1]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h1, hc35, hlam, hphi, ht12, ht23, p180_1, u1ehi2]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht12, ht23, p180_1, u1ehi2]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    rcases p180_3 (m.d 0 3) (by simp) with h205 | h205
                                    · linarith only [h153, h205, hlam]
                                    · linarith only [h2, h205, hlam]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h179, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                                · linarith only [h1, h155, h179, h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                              · linarith only [h157, h173, h178, hlam]
                        · linarith only [h155, h173, h3, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h156, h2, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h214 | h214
              · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
                · rcases m.htr 1 2 5 (by decide) (by decide) with h216 | h216
                  · linarith only [h0, h216, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h218 | h218
                    · linarith only [h1, h218, h3, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                      · linarith only [h1, h153, h220, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h222 | h222
                        · linarith only [h1, h155, h222, h3, hc14, hlam, hphi, u1ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                          · linarith only [h1, h214, h216, h224, h3, hc25, hlam, hphi, ht12, u1ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                            · linarith only [h1, h153, h215, h216, h224, h226, hc25, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                              · linarith only [h215, h216, h226, h228, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h230 | h230
                                · linarith only [h215, h216, h224, h228, h230, hc23, hc34, hlam, hphi]
                                · linarith only [h1, h230, h3, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h233 | h233
                  · linarith only [h0, h233, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
                    · linarith only [h1, h235, h3, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                      · linarith only [h1, h237, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
                        · linarith only [h1, h155, h239, h3, hc14, hlam, hphi, u1ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h241 | h241
                          · linarith only [h1, h2, h241, h3, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h243 | h243
                            · linarith only [h1, h153, h214, h215, h239, h243, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
                              · linarith only [h214, h215, h239, h241, h245, hc23, hc34, hlam, hphi]
                              · linarith only [h214, h215, h245, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h2, h214, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h249 | h249
        · rcases m.htr 0 3 5 (by decide) (by decide) with h250 | h250
          · rcases m.htr 0 4 5 (by decide) (by decide) with h251 | h251
            · rcases m.htr 1 2 3 (by decide) (by decide) with h252 | h252
              · linarith only [h0, h2, h252, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h254 | h254
                · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
                  · linarith only [h0, h255, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h258 | h258
                      · linarith only [h1, h258, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h2, h250, h258, hc23, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h2, h249, h252, h257, hc23, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h254, h262, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
                      · linarith only [h1, h265, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h2, h250, h265, hc23, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h2, h249, h252, h264, hc23, hlam, hphi, ht12, u1ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
              · linarith only [h2, h250, h269, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
                · rcases m.htr 1 2 5 (by decide) (by decide) with h272 | h272
                  · linarith only [h0, h2, h272, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h275 | h275
                      · linarith only [h1, h275, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h2, h250, h275, hc23, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h2, h249, h269, h274, hc23, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
                  · linarith only [h271, h279, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h282 | h282
                      · linarith only [h1, h282, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h2, h250, h282, hc23, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h2, h249, h269, h281, hc23, hlam, hphi, ht12, u1ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
            · linarith only [h249, h250, h286, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
              · linarith only [h0, h2, h288, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h290 | h290
                · rcases m.htr 1 2 5 (by decide) (by decide) with h291 | h291
                  · linarith only [h0, h2, h291, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h293 | h293
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h294 | h294
                      · linarith only [h1, h250, h294, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h296 | h296
                        · linarith only [h1, h250, h288, h290, h296, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h298 | h298
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h299 | h299
                            · linarith only [h1, h250, h288, h299, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h2, h290, h299, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h0, h2, h290, h298, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · linarith only [h2, h249, h288, h290, h293, hc23, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                  · linarith only [h290, h304, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                      · linarith only [h1, h250, h307, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                        · linarith only [h1, h250, h306, h309, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                            · linarith only [h1, h250, h290, h306, h312, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h2, h312, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h0, h1, h2, h306, h311, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · linarith only [h249, h250, h306, hc35, hlam, hphi, ht12, ht23, u1ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h317 | h317
          · linarith only [h249, h317, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h319 | h319
            · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
              · linarith only [h0, h2, h320, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
                · rcases m.htr 1 2 5 (by decide) (by decide) with h323 | h323
                  · linarith only [h0, h2, h323, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h325 | h325
                    · linarith only [h1, h249, h325, hlam]
                    · linarith only [h320, h322, h325, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h328 | h328
                  · linarith only [h1, h249, h320, h328, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
                    · linarith only [h1, h249, h330, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
                      · linarith only [h1, h317, h332, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h334 | h334
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                          · linarith only [h1, h249, h320, h335, hc23, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h0, h2, h335, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h249, h319, h334, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
              · linarith only [h0, h2, h339, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                  · linarith only [h0, h2, h342, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                    · linarith only [h1, h249, h344, hlam]
                    · linarith only [h339, h341, h344, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h347 | h347
                  · linarith only [h341, h347, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h349 | h349
                    · linarith only [h1, h249, h349, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h351 | h351
                      · linarith only [h1, h249, h317, h319, h351, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h353 | h353
                        · linarith only [h1, h249, h319, h339, h353, hc14, hlam, hphi, u1ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                          · linarith only [h1, h249, h339, h355, hc23, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h0, h2, h355, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h359 | h359
    · linarith only [h0, h359, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h361 | h361
      · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
        · rcases m.htr 0 3 5 (by decide) (by decide) with h363 | h363
          · rcases m.htr 0 4 5 (by decide) (by decide) with h364 | h364
            · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
              · rcases m.htr 1 2 4 (by decide) (by decide) with h366 | h366
                · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h369 | h369
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h371 | h371
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h372 | h372
                            · linarith only [h361, h372, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h374 | h374
                              · linarith only [h359, h363, h365, h371, h372, h374, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h376 | h376
                                · linarith only [h359, h363, h365, h371, h372, h374, h376, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                                · rcases h3bigk with h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h359, hlam, p378_1]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    rcases p378_3 (m.d 0 3) (by simp) with h381 | h381
                                    · rcases p378_3 (m.d 1 3) (by simp) with h382 | h382
                                      · rcases p378_3 (m.d 2 3) (by simp) with h383 | h383
                                        · linarith only [h361, h383, hlam]
                                        · rcases p378_3 (m.d 3 4) (by simp) with h385 | h385
                                          · linarith only [h362, h385, hlam]
                                          · rcases p378_3 (m.d 3 5) (by simp) with h387 | h387
                                            · linarith only [h363, h387, hlam]
                                            · linarith only [h372, h387, hlam]
                                      · linarith only [h365, h382, hlam]
                                    · linarith only [h361, h381, hlam]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h362, h364, h371, h372, h376, hlam, p378_2]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h359, h365, h371, h372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p378_1]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h362, h364, h365, hc12, hlam, hphi, ht01, ht0b, ht5b, p378_1, u5ehi4]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    rcases p378_3 (m.d 0 3) (by simp) with h396 | h396
                                    · linarith only [h359, h396, hlam]
                                    · linarith only [h361, h396, hlam]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h359, h362, h364, h371, h372, h376, hlam, p378_2]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h371, h372, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p378_1]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h361, hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h365, hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h362, h364, h372, h376, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p378_1]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h372, hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h362, hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h368, hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h371, hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h376, hlam, p378_1]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h363, hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h369, hlam, p378_0]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [h0, h361, h362, h364, h371, h376, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p378_1]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    rcases p378_3 (m.d 0 3) (by simp) with h414 | h414
                                    · rcases p378_3 (m.d 1 3) (by simp) with h415 | h415
                                      · rcases p378_3 (m.d 2 3) (by simp) with h416 | h416
                                        · linarith only [h372, h416, hlam]
                                        · linarith only [h371, h416, hlam]
                                      · linarith only [h368, h415, hlam]
                                    · linarith only [h362, h414, hlam]
                                  · have p378_0 := h378c.1
                                    have p378_1 := h378c.2.1
                                    have p378_2 := h378c.2.2.1
                                    have p378_3 := h378c.2.2.2
                                    linarith only [hlam, p378_0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h422 | h422
                            · linarith only [h371, h422, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h424 | h424
                              · linarith only [h366, h424, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h426 | h426
                                · linarith only [h0, h361, h362, h426, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                · rcases h3bigk with h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h359, hlam, p428_1]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h362, h364, h371, h426, hlam, p428_2]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    rcases p428_3 (m.d 0 3) (by simp) with h432 | h432
                                    · rcases p428_3 (m.d 1 3) (by simp) with h433 | h433
                                      · rcases p428_3 (m.d 2 3) (by simp) with h434 | h434
                                        · linarith only [h361, h434, hlam]
                                        · rcases p428_3 (m.d 3 4) (by simp) with h436 | h436
                                          · linarith only [h436, hlam, p428_0]
                                          · rcases p428_3 (m.d 3 5) (by simp) with h438 | h438
                                            · linarith only [h363, h438, hlam]
                                            · linarith only [h426, h438, hlam]
                                      · linarith only [h368, h433, hlam]
                                    · linarith only [h432, hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h422, hc03, hlam, hphi, ht0b, ht5b, p428_1, u5ehi2]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h359, hc13, hlam, hphi, p428_1, u1ehi0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h359, h362, h364, h371, h426, hlam, p428_2]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    rcases p428_3 (m.d 0 3) (by simp) with h447 | h447
                                    · linarith only [h359, h447, hlam]
                                    · linarith only [h362, h447, hlam]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h422, hc13, hlam, hphi, ht01, ht0b, ht5b, p428_1, u5ehi2]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h361, hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h365, hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h371, hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h422, hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h362, hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h368, hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h362, h364, h426, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p428_1]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h426, hlam, p428_1]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h363, hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h369, hlam, p428_0]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    rcases p428_3 (m.d 0 3) (by simp) with h463 | h463
                                    · rcases p428_3 (m.d 1 3) (by simp) with h464 | h464
                                      · rcases p428_3 (m.d 2 3) (by simp) with h465 | h465
                                        · linarith only [h465, hlam, p428_0]
                                        · rcases p428_3 (m.d 3 4) (by simp) with h467 | h467
                                          · linarith only [h426, h467, hlam]
                                          · linarith only [h371, h467, hlam]
                                      · linarith only [h365, h464, hlam]
                                    · linarith only [h361, h463, hlam]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [h0, h361, h363, h371, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p428_1]
                                  · have p428_0 := h428c.1
                                    have p428_1 := h428c.2.1
                                    have p428_2 := h428c.2.2.1
                                    have p428_3 := h428c.2.2.2
                                    linarith only [hlam, p428_0]
                        · linarith only [h0, h361, h362, h364, h370, hc12, hlam, hphi, u1ehi3]
                      · linarith only [h0, h361, h363, h369, hc12, hlam, hphi, u1ehi2]
                    · linarith only [h359, h363, h368, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · linarith only [h0, h367, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h361, h362, h364, h366, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · linarith only [h0, h361, h362, h364, h365, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h480 | h480
              · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
                · rcases m.htr 1 2 5 (by decide) (by decide) with h482 | h482
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h483 | h483
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h484 | h484
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h485 | h485
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h486 | h486
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h487 | h487
                            · linarith only [h361, h487, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h489 | h489
                              · linarith only [h363, h364, h486, h487, h489, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h491 | h491
                                · linarith only [h363, h364, h486, h487, h491, hlam]
                                · rcases h3bigk with h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h359, hlam, p493_1]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    rcases p493_3 (m.d 0 3) (by simp) with h496 | h496
                                    · rcases p493_3 (m.d 1 3) (by simp) with h497 | h497
                                      · rcases p493_3 (m.d 2 3) (by simp) with h498 | h498
                                        · linarith only [h361, h498, hlam]
                                        · rcases p493_3 (m.d 3 4) (by simp) with h500 | h500
                                          · linarith only [h362, h500, hlam]
                                          · rcases p493_3 (m.d 3 5) (by simp) with h502 | h502
                                            · linarith only [h363, h502, hlam]
                                            · linarith only [h487, h502, hlam]
                                      · linarith only [h480, h497, hlam]
                                    · linarith only [h361, h496, hlam]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h363, h486, h487, hlam, p493_2]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h486, h487, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p493_1]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h359, hc13, hlam, hphi, p493_1, u1ehi0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    rcases p493_3 (m.d 0 3) (by simp) with h511 | h511
                                    · linarith only [h359, h511, hlam]
                                    · linarith only [h361, h511, hlam]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h359, h363, h486, h487, hlam, p493_2]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h486, h487, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p493_1]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h361, hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h480, hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h363, h487, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p493_1]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h487, hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h362, hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h483, hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h486, hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h491, hlam, p493_1]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h363, hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h484, hlam, p493_0]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [h363, h364, h480, h483, h485, h486, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p493_1]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    rcases p493_3 (m.d 0 3) (by simp) with h529 | h529
                                    · rcases p493_3 (m.d 1 3) (by simp) with h530 | h530
                                      · rcases p493_3 (m.d 2 3) (by simp) with h531 | h531
                                        · linarith only [h487, h531, hlam]
                                        · linarith only [h486, h531, hlam]
                                      · linarith only [h483, h530, hlam]
                                    · linarith only [h362, h529, hlam]
                                  · have p493_0 := h493c.1
                                    have p493_1 := h493c.2.1
                                    have p493_2 := h493c.2.2.1
                                    have p493_3 := h493c.2.2.2
                                    linarith only [hlam, p493_0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h537 | h537
                            · linarith only [h486, h537, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h539 | h539
                              · linarith only [h362, h364, h481, h486, h539, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h541 | h541
                                · linarith only [h362, h364, h541, hlam]
                                · rcases h3bigk with h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h359, hlam, p543_1]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    rcases p543_3 (m.d 0 3) (by simp) with h546 | h546
                                    · rcases p543_3 (m.d 1 3) (by simp) with h547 | h547
                                      · rcases p543_3 (m.d 2 3) (by simp) with h548 | h548
                                        · linarith only [h361, h548, hlam]
                                        · rcases p543_3 (m.d 3 4) (by simp) with h550 | h550
                                          · linarith only [h362, h550, hlam]
                                          · linarith only [h486, h550, hlam]
                                      · linarith only [h480, h547, hlam]
                                    · linarith only [h361, h546, hlam]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    rcases p543_3 (m.d 0 3) (by simp) with h555 | h555
                                    · rcases p543_3 (m.d 1 3) (by simp) with h556 | h556
                                      · rcases p543_3 (m.d 2 3) (by simp) with h557 | h557
                                        · linarith only [h361, h557, hlam]
                                        · rcases p543_3 (m.d 3 4) (by simp) with h559 | h559
                                          · linarith only [h559, hlam, p543_0]
                                          · rcases p543_3 (m.d 3 5) (by simp) with h561 | h561
                                            · linarith only [h363, h561, hlam]
                                            · linarith only [h541, h561, hlam]
                                      · linarith only [h483, h556, hlam]
                                    · linarith only [h555, hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h537, hc03, hlam, hphi, ht0b, ht5b, p543_1, u5ehi2]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h359, h480, hc12, hlam, hphi, p543_1, u1ehi0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h362, h364, h483, h485, h486, hlam, p543_2]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    rcases p543_3 (m.d 0 3) (by simp) with h570 | h570
                                    · linarith only [h359, h570, hlam]
                                    · linarith only [h362, h570, hlam]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [hc13, hlam, hphi, ht01, ht0b, ht5b, p543_1, u5ehi3]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h361, hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h480, hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h486, hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h537, hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h362, hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h483, hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h362, h364, h485, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p543_1]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h541, hlam, p543_1]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h363, hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h484, hlam, p543_0]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    rcases p543_3 (m.d 0 3) (by simp) with h586 | h586
                                    · rcases p543_3 (m.d 1 3) (by simp) with h587 | h587
                                      · rcases p543_3 (m.d 2 3) (by simp) with h588 | h588
                                        · linarith only [h588, hlam, p543_0]
                                        · rcases p543_3 (m.d 3 4) (by simp) with h590 | h590
                                          · linarith only [h541, h590, hlam]
                                          · linarith only [h486, h590, hlam]
                                      · linarith only [h480, h587, hlam]
                                    · linarith only [h361, h586, hlam]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [h363, h364, h480, h483, h485, h486, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p543_1]
                                  · have p543_0 := h543c.1
                                    have p543_1 := h543c.2.1
                                    have p543_2 := h543c.2.2.1
                                    have p543_3 := h543c.2.2.2
                                    linarith only [hlam, p543_0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h597 | h597
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h598 | h598
                            · linarith only [h0, h361, h598, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h600 | h600
                              · linarith only [h485, h600, hc24, hlam, hphi, ht12, u1ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h602 | h602
                                · linarith only [h485, h602, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                · rcases h3bigk with h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h359, hlam, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    rcases p604_3 (m.d 0 3) (by simp) with h607 | h607
                                    · rcases p604_3 (m.d 1 3) (by simp) with h608 | h608
                                      · rcases p604_3 (m.d 2 3) (by simp) with h609 | h609
                                        · linarith only [h361, h609, hlam]
                                        · rcases p604_3 (m.d 3 4) (by simp) with h611 | h611
                                          · linarith only [h362, h611, hlam]
                                          · rcases p604_3 (m.d 3 5) (by simp) with h613 | h613
                                            · linarith only [h363, h613, hlam]
                                            · linarith only [h598, h613, hlam]
                                      · linarith only [h480, h608, hlam]
                                    · linarith only [h361, h607, hlam]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h363, h597, h598, hlam, p604_2]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h0, h361, h597, h598, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h359, h480, hc12, hlam, hphi, p604_1, u1ehi0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    rcases p604_3 (m.d 0 3) (by simp) with h622 | h622
                                    · linarith only [h359, h622, hlam]
                                    · linarith only [h361, h622, hlam]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h359, h363, h597, h598, hlam, p604_2]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h597, h598, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h361, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h480, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h363, h598, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h598, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h362, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h483, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h597, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h602, hlam, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h363, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h484, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h0, h361, h363, h597, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    rcases p604_3 (m.d 0 3) (by simp) with h640 | h640
                                    · rcases p604_3 (m.d 1 3) (by simp) with h641 | h641
                                      · rcases p604_3 (m.d 2 3) (by simp) with h642 | h642
                                        · linarith only [h598, h642, hlam]
                                        · linarith only [h597, h642, hlam]
                                      · linarith only [h483, h641, hlam]
                                    · linarith only [h362, h640, hlam]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h648 | h648
                            · linarith only [h597, h648, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h650 | h650
                              · linarith only [h364, h481, h650, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h652 | h652
                                · linarith only [h485, h652, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                · rcases h3bigk with h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h359, hlam, p654_1]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    rcases p654_3 (m.d 0 3) (by simp) with h657 | h657
                                    · rcases p654_3 (m.d 1 3) (by simp) with h658 | h658
                                      · rcases p654_3 (m.d 2 3) (by simp) with h659 | h659
                                        · linarith only [h361, h659, hlam]
                                        · rcases p654_3 (m.d 3 4) (by simp) with h661 | h661
                                          · linarith only [h362, h661, hlam]
                                          · linarith only [h597, h661, hlam]
                                      · linarith only [h480, h658, hlam]
                                    · linarith only [h361, h657, hlam]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    rcases p654_3 (m.d 0 3) (by simp) with h666 | h666
                                    · rcases p654_3 (m.d 1 3) (by simp) with h667 | h667
                                      · rcases p654_3 (m.d 2 3) (by simp) with h668 | h668
                                        · linarith only [h361, h668, hlam]
                                        · rcases p654_3 (m.d 3 4) (by simp) with h670 | h670
                                          · linarith only [h670, hlam, p654_0]
                                          · rcases p654_3 (m.d 3 5) (by simp) with h672 | h672
                                            · linarith only [h363, h672, hlam]
                                            · linarith only [h652, h672, hlam]
                                      · linarith only [h483, h667, hlam]
                                    · linarith only [h666, hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h359, h480, h648, hc12, hlam, hphi, ht01, ht0b, ht5b, p654_1, u5ehi2]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h359, h480, hc12, hlam, hphi, p654_1, u1ehi0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    rcases p654_3 (m.d 0 3) (by simp) with h680 | h680
                                    · linarith only [h359, h680, hlam]
                                    · linarith only [h361, h680, hlam]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    rcases p654_3 (m.d 0 3) (by simp) with h683 | h683
                                    · linarith only [h359, h683, hlam]
                                    · linarith only [h362, h683, hlam]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h480, h648, hc12, hlam, hphi, ht01, ht0b, ht5b, p654_1, u5ehi2]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h361, hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h480, hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h597, hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h648, hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h362, hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h483, hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h362, h364, hc23, hc45, hlam, hphi, ht34, p654_1]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h652, hlam, p654_1]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h363, hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h484, hlam, p654_0]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    rcases p654_3 (m.d 0 3) (by simp) with h699 | h699
                                    · rcases p654_3 (m.d 1 3) (by simp) with h700 | h700
                                      · rcases p654_3 (m.d 2 3) (by simp) with h701 | h701
                                        · linarith only [h701, hlam, p654_0]
                                        · rcases p654_3 (m.d 3 4) (by simp) with h703 | h703
                                          · linarith only [h652, h703, hlam]
                                          · linarith only [h597, h703, hlam]
                                      · linarith only [h480, h700, hlam]
                                    · linarith only [h361, h699, hlam]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [h363, h597, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p654_1]
                                  · have p654_0 := h654c.1
                                    have p654_1 := h654c.2.1
                                    have p654_2 := h654c.2.2.1
                                    have p654_3 := h654c.2.2.2
                                    linarith only [hlam, p654_0]
                      · linarith only [h359, h363, h484, hlam]
                    · linarith only [h359, h363, h483, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · linarith only [h0, h482, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h361, h363, h481, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h0, h361, h363, h480, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h715 | h715
            · linarith only [h362, h363, h715, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h717 | h717
              · rcases m.htr 1 2 4 (by decide) (by decide) with h718 | h718
                · rcases m.htr 1 2 5 (by decide) (by decide) with h719 | h719
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h720 | h720
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h721 | h721
                      · linarith only [h359, h363, h717, h721, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h359, h721, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h359, h361, h362, h720, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · linarith only [h0, h719, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h359, h717, h718, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h361, h717, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h728 | h728
          · linarith only [h362, h728, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h730 | h730
            · rcases m.htr 1 2 3 (by decide) (by decide) with h731 | h731
              · rcases m.htr 1 2 4 (by decide) (by decide) with h732 | h732
                · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h734 | h734
                    · linarith only [h359, h362, h734, hc13, hlam, hphi, u1ehi0]
                    · linarith only [h359, h734, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h733, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h359, h731, h732, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h361, h731, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
              · rcases m.htr 1 2 4 (by decide) (by decide) with h741 | h741
                · rcases m.htr 1 2 5 (by decide) (by decide) with h742 | h742
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h743 | h743
                    · linarith only [h359, h362, h743, hc13, hlam, hphi, u1ehi0]
                    · linarith only [h359, h743, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h742, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h741, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h361, h740, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h749 | h749
        · rcases m.htr 0 3 5 (by decide) (by decide) with h750 | h750
          · rcases m.htr 0 4 5 (by decide) (by decide) with h751 | h751
            · rcases m.htr 1 2 3 (by decide) (by decide) with h752 | h752
              · linarith only [h0, h361, h752, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h752, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h755 | h755
              · linarith only [h0, h361, h755, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h755, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h758 | h758
            · linarith only [h749, h750, h758, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
              · linarith only [h0, h361, h760, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h760, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h763 | h763
          · linarith only [h749, h763, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h765 | h765
            · rcases m.htr 1 2 3 (by decide) (by decide) with h766 | h766
              · linarith only [h0, h361, h766, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h766, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h769 | h769
              · linarith only [h0, h361, h769, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h769, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
