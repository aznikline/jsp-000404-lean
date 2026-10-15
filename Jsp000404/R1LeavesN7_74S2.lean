import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_R_L_R_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
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
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h15, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h12, h15, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                                · linarith only [h0, h18, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h12, h18, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h0, h12, h13, h3, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                            · linarith only [h12, h22, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                                · linarith only [h0, h12, h25, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                                  · linarith only [h0, h22, h27, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                                    · linarith only [h0, h10, h29, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h1, h24, h29, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                                · linarith only [h0, h12, h24, h3, h32, h6, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                                  · linarith only [h0, h22, h3, h34, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                                    · linarith only [h10, h24, h36, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
                                      · linarith only [h10, h24, h38, hc34, hlam, hphi, ht23, u2ehi3]
                                      · linarith only [h0, h12, h3, h38, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h11, h5, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h9, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                      · linarith only [h43, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                        · linarith only [h0, h3, h45, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                                      · linarith only [h0, h3, h47, h53, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · linarith only [h1, h49, h53, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                    · linarith only [h43, h49, h52, hlam]
                                  · linarith only [h48, h51, h9, hlam]
                                · linarith only [h48, h50, h9, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                                    · linarith only [h43, h49, h59, h61, hc23, hlam, hphi, u2ehi1]
                                    · linarith only [h43, h6, h61, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h3, h60, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h47, h59, h9, hlam]
                            · linarith only [h47, h48, hc35, hlam, hphi, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h67 | h67
                            · linarith only [h47, h67, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                                · linarith only [h0, h3, h47, h70, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · linarith only [h0, h3, h6, h70, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                                · linarith only [h0, h3, h47, h73, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h3, h6, h73, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h80 | h80
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                              · linarith only [h8, h81, hc14, hlam, hphi, ht01, u0ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                                · linarith only [h0, h76, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h6, h8, h83, hc45, hlam, hphi, ht34, u3ehi2]
                            · linarith only [h79, h80, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h6, h79, h8, hc45, hlam, hphi, ht34, u3ehi1]
                        · linarith only [h0, h5, h76, h78, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h76, h77, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                      · linarith only [h76, h90, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h4, h8, h90, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h94 | h94
                · linarith only [h6, h94, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h96 | h96
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                          · linarith only [h100, h6, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                            · linarith only [h102, h94, hc13, hlam, hphi, ht01, u0ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                                · linarith only [h0, h105, h97, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                                  · linarith only [h0, h105, h107, h94, h98, hc01, hlam, hphi, u0ehi2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h109 | h109
                                    · linarith only [h0, h109, h98, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h105, h109, h6, h96, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h104, h6, h96, h98, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h5, h97, h99, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h97, h98, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h94, h97, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                          · linarith only [h119, h6, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                            · linarith only [h1, h119, h121, h94, hc04, hlam, hphi, u0ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                              · linarith only [h1, h123, h96, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                                · linarith only [h0, h116, h119, h125, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h127 | h127
                                  · linarith only [h1, h116, h119, h127, h94, h96, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
                                    · linarith only [h0, h117, h129, h96, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                                      · linarith only [h0, h118, h125, h129, h131, h6, h96, hc01, hc34, hlam, hphi, ht23, u0ehi2, u2ehi2]
                                      · linarith only [h0, h118, h125, h129, h131, h6, hc01, hc45, hlam, hphi, ht23, ht34, u0ehi2, u2ehi2]
                        · linarith only [h0, h116, h118, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h116, h117, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h116, h3, h6, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h139 | h139
          · linarith only [h139, h3, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h141 | h141
            · linarith only [h141, h3, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h143 | h143
              · rcases m.htr 0 3 5 (by decide) (by decide) with h144 | h144
                · rcases m.htr 0 4 5 (by decide) (by decide) with h145 | h145
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                    · linarith only [h146, h3, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
                      · linarith only [h0, h139, h148, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                        · linarith only [h0, h141, h150, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                                      · rcases h5bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h139, h145, h150, hc24, hlam, hphi, p159_1, u2ehi1]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h141, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          rcases p159_3 (m.d 0 5) (by simp) with h163 | h163
                                          · rcases p159_3 (m.d 1 5) (by simp) with h164 | h164
                                            · linarith only [h164, h2, hlam]
                                            · linarith only [h153, h164, hlam]
                                          · linarith only [h144, h163, hlam]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          rcases p159_3 (m.d 0 5) (by simp) with h168 | h168
                                          · rcases p159_3 (m.d 1 5) (by simp) with h169 | h169
                                            · linarith only [h169, h2, hlam]
                                            · linarith only [h154, h169, hlam]
                                          · linarith only [h145, h168, hlam]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h2, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h150, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1, u3ehi4]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h1, h154, hc01, hlam, hphi, ht0b, ht5b, p159_1, u5ehi4]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h155, h157, hc23, hlam, hphi, ht01, ht12, p159_1, u0ehi4]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h150, h155, h157, hc23, hlam, hphi, p159_1, u2ehi1]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          rcases p159_3 (m.d 0 5) (by simp) with h181 | h181
                                          · linarith only [h141, h181, hlam]
                                          · linarith only [h144, h181, hlam]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          rcases p159_3 (m.d 0 5) (by simp) with h184 | h184
                                          · linarith only [h141, h184, hlam]
                                          · linarith only [h145, h184, hlam]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h144, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h153, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h156, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h144, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p159_1, u5ehi4]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h145, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h154, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h157, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [h158, hlam, p159_0]
                                        · have p159_0 := h159c.1
                                          have p159_1 := h159c.2.1
                                          have p159_2 := h159c.2.2.1
                                          have p159_3 := h159c.2.2.2
                                          linarith only [hlam, p159_0]
                                      · linarith only [h1, h154, h158, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                    · linarith only [h1, h154, h157, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h156, h3, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                                · linarith only [h143, h155, h3, hc03, hlam, hphi, u0ehi1]
                              · linarith only [h143, h145, h148, h154, h3, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h144, h146, h153, h3, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h143, h146, h152, h3, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
                    · linarith only [h0, h144, h204, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h206 | h206
                      · linarith only [h0, h139, h206, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h208 | h208
                        · linarith only [h0, h139, h208, hc24, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h211 | h211
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
                              · linarith only [h1, h145, h212, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h216 | h216
                                    · linarith only [h139, h145, h214, h216, hc23, hlam, hphi, u2ehi0]
                                    · linarith only [h139, h216, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                                  · linarith only [h215, h3, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                                · linarith only [h143, h214, h3, hc03, hlam, hphi, u0ehi1]
                            · linarith only [h144, h204, h211, h3, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h143, h204, h210, h3, hc23, hlam, hphi, u2ehi1]
                · linarith only [h143, h144, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h224 | h224
                · linarith only [h143, h224, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
                    · linarith only [h0, h139, h227, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h229 | h229
                      · linarith only [h0, h143, h229, h3, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h231 | h231
                        · linarith only [h0, h141, h231, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h233 | h233
                          · linarith only [h143, h233, h3, hc13, hlam, hphi, ht01, u0ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h235 | h235
                            · linarith only [h224, h235, h3, hc13, hlam, hphi, ht01, u0ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h238 | h238
                                · linarith only [h143, h238, h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                                · linarith only [h238, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                              · linarith only [h139, h226, h229, h237, hc24, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                    · linarith only [h0, h143, h226, h242, h3, hc45, hlam, hphi, ht34, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                      · linarith only [h0, h139, h244, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h246 | h246
                        · linarith only [h0, h141, h143, h226, h246, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
                          · linarith only [h143, h248, h3, hc13, hlam, hphi, ht01, u0ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h250 | h250
                            · linarith only [h1, h224, h248, h250, h3, hc04, hlam, hphi, u0ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h252 | h252
                              · linarith only [h1, h226, h252, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                                · linarith only [h143, h254, h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                                · linarith only [h254, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h257 | h257
        · rcases m.htr 0 2 4 (by decide) (by decide) with h258 | h258
          · rcases m.htr 0 2 5 (by decide) (by decide) with h259 | h259
            · linarith only [h0, h2, h259, hlam]
            · linarith only [h257, h259, hc25, hlam, hphi, u2ehi2]
          · linarith only [h257, h258, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h263 | h263
          · linarith only [h257, h263, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h265 | h265
            · linarith only [h257, h265, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h267 | h267
              · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
                · rcases m.htr 0 4 5 (by decide) (by decide) with h269 | h269
                  · linarith only [h1, h2, h269, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                    · linarith only [h0, h257, h271, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                      · linarith only [h0, h2, h263, h273, hc15, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
                        · linarith only [h1, h2, h273, h275, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · linarith only [h1, h2, h273, h275, hc25, hlam, hphi, u2ehi1]
                · linarith only [h267, h268, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h279 | h279
                · linarith only [h267, h279, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h281 | h281
                  · linarith only [h1, h2, h281, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
                    · linarith only [h0, h2, h283, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
                      · linarith only [h0, h2, h263, h285, hc15, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
                        · linarith only [h1, h2, h285, h287, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · linarith only [h1, h2, h285, h287, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h290 | h290
      · rcases m.htr 0 2 3 (by decide) (by decide) with h291 | h291
        · rcases m.htr 0 2 4 (by decide) (by decide) with h292 | h292
          · linarith only [h0, h1, h292, hlam]
          · linarith only [h291, h292, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h295 | h295
          · linarith only [h291, h295, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h297 | h297
            · linarith only [h291, h297, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h299 | h299
              · rcases m.htr 0 3 5 (by decide) (by decide) with h300 | h300
                · rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                    · linarith only [h291, h302, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                      · linarith only [h0, h291, h304, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h0, h1, h304, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h1, h301, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h299, h300, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h309 | h309
                · linarith only [h299, h309, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h311 | h311
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h312 | h312
                    · linarith only [h0, h291, h312, hc01, hlam, hphi, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h314 | h314
                      · linarith only [h0, h1, h314, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h1, h314, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h1, h311, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h318 | h318
        · rcases m.htr 0 2 4 (by decide) (by decide) with h319 | h319
          · linarith only [h0, h1, h319, hlam]
          · linarith only [h318, h319, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h322 | h322
          · linarith only [h318, h322, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h324 | h324
            · linarith only [h318, h324, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h326 | h326
              · rcases m.htr 0 3 5 (by decide) (by decide) with h327 | h327
                · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
                    · linarith only [h0, h318, h329, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                      · linarith only [h0, h1, h331, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h1, h331, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h1, h328, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h326, h327, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h336 | h336
                · linarith only [h326, h336, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
                    · linarith only [h0, h318, h339, hc01, hlam, hphi, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                      · linarith only [h0, h1, h341, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h1, h341, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h1, h338, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h345 | h345
    · rcases m.htr 0 1 5 (by decide) (by decide) with h346 | h346
      · rcases m.htr 0 2 3 (by decide) (by decide) with h347 | h347
        · rcases m.htr 0 2 4 (by decide) (by decide) with h348 | h348
          · rcases m.htr 0 2 5 (by decide) (by decide) with h349 | h349
            · rcases m.htr 0 3 4 (by decide) (by decide) with h350 | h350
              · rcases m.htr 0 3 5 (by decide) (by decide) with h351 | h351
                · rcases m.htr 0 4 5 (by decide) (by decide) with h352 | h352
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h355 | h355
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h356 | h356
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h357 | h357
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h358 | h358
                              · linarith only [h0, h345, h358, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h345, h352, h354, h358, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h351, h356, h357, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
                            · linarith only [h356, h362, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                              · linarith only [h0, h345, h364, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h345, h352, h354, h364, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h346, h355, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h346, h354, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h345, h352, h353, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                              · linarith only [h0, h345, h352, h375, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h378 | h378
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h379 | h379
                                    · linarith only [h0, h346, h352, h371, h375, h379, hc12, hlam, hphi, ht01, u0ehi3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h381 | h381
                                      · linarith only [h0, h346, h352, h371, h375, h377, h381, hc12, hlam, hphi, ht01, u0ehi3]
                                      · rcases h5bigk with h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [hlam, p383_0]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h0, h346, h371, h375, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p383_1, u2ehi3]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h0, h346, hc12, hlam, hphi, ht01, ht0b, ht5b, p383_1, u5ehi2]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h0, h346, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p383_1, u3ehi4]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h352, hlam, p383_1]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h346, hlam, p383_0]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [hlam, p383_0]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h0, h346, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p383_1, u2ehi4]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h0, h346, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p383_1, u3ehi4]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h375, hlam, p383_1]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h349, hlam, p383_1]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h372, hlam, p383_1]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [hlam, p383_0]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h0, h349, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p383_1, u3ehi4]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h379, hlam, p383_1]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h351, hlam, p383_0]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h374, hlam, p383_0]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h378, hlam, p383_0]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [hlam, p383_0]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h381, hlam, p383_1]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p383_1, u0ehi4]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [h372, hc45, hlam, hphi, ht23, ht34, p383_1, u2ehi4]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [hc45, hlam, hphi, ht23, ht34, p383_1, u2ehi4]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [hc45, hlam, hphi, ht34, p383_1, u3ehi4]
                                        · have p383_0 := h383c.1
                                          have p383_1 := h383c.2.1
                                          have p383_2 := h383c.2.2.1
                                          have p383_3 := h383c.2.2.2
                                          linarith only [hlam, p383_0]
                                  · linarith only [h0, h346, h374, h378, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h350, h352, h377, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h373, h374, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h350, h352, h373, hc45, hlam, hphi, ht34, u3ehi1]
                        · linarith only [h0, h345, h371, h372, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h0, h346, h371, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h346, h370, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h350, h351, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h417 | h417
                · linarith only [h350, h417, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h419 | h419
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h422 | h422
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
                          · linarith only [h350, h423, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h425 | h425
                            · linarith only [h345, h417, h423, h425, hc01, hlam, hphi, u0ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h427 | h427
                              · linarith only [h0, h345, h427, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h345, h419, h420, h423, h427, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h346, h422, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h346, h421, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h345, h417, h419, h420, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h433 | h433
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h434 | h434
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h435 | h435
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h436 | h436
                          · linarith only [h350, h436, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h438 | h438
                            · linarith only [h345, h417, h436, h438, hc01, hlam, hphi, u0ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h440 | h440
                              · linarith only [h0, h345, h350, h419, h440, hc12, hlam, hphi, ht01, u0ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h442 | h442
                                · linarith only [h0, h346, h350, h433, h436, h440, h442, hc12, hlam, hphi, ht01, u0ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h444 | h444
                                  · linarith only [h0, h346, h417, h433, h436, h440, h444, hc12, hlam, hphi, ht01, u0ehi2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h446 | h446
                                    · linarith only [h350, h419, h446, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h448 | h448
                                      · linarith only [h0, h346, h350, h419, h433, h436, h440, h448, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi2, u2ehi2]
                                      · linarith only [h0, h346, h350, h433, h436, h440, h448, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi2, u2ehi2]
                        · linarith only [h0, h346, h435, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h346, h434, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h346, h433, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h347, h349, hc25, hlam, hphi, u2ehi2]
          · linarith only [h347, h348, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h456 | h456
          · linarith only [h347, h456, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h345, h456, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h459 | h459
        · rcases m.htr 0 2 4 (by decide) (by decide) with h460 | h460
          · rcases m.htr 0 2 5 (by decide) (by decide) with h461 | h461
            · rcases m.htr 0 3 4 (by decide) (by decide) with h462 | h462
              · rcases m.htr 0 3 5 (by decide) (by decide) with h463 | h463
                · rcases m.htr 0 4 5 (by decide) (by decide) with h464 | h464
                  · linarith only [h345, h346, h464, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h466 | h466
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h467 | h467
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h468 | h468
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h470 | h470
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h471 | h471
                              · linarith only [h345, h346, h464, h466, h470, h471, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h345, h346, h467, h471, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                            · linarith only [h463, h469, h470, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h462, h464, h469, hc45, hlam, hphi, ht34, u3ehi1]
                        · linarith only [h0, h345, h467, h468, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h0, h461, h467, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h466, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h462, h463, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h480 | h480
                · linarith only [h462, h480, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h482 | h482
                  · linarith only [h345, h346, h482, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h484 | h484
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h485 | h485
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h486 | h486
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
                          · linarith only [h462, h487, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h489 | h489
                            · linarith only [h345, h480, h487, h489, hc01, hlam, hphi, u0ehi2]
                            · linarith only [h345, h346, h487, h489, hc35, hlam, hphi, u3ehi1]
                        · linarith only [h0, h345, h461, h485, h486, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h461, h485, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h345, h462, h484, hc23, hlam, hphi, ht01, ht12, u0ehi2]
            · linarith only [h459, h461, hc25, hlam, hphi, u2ehi2]
          · linarith only [h459, h460, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h497 | h497
          · linarith only [h459, h497, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h345, h497, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h500 | h500
      · rcases m.htr 0 2 3 (by decide) (by decide) with h501 | h501
        · rcases m.htr 0 2 4 (by decide) (by decide) with h502 | h502
          · rcases m.htr 0 2 5 (by decide) (by decide) with h503 | h503
            · rcases m.htr 0 3 4 (by decide) (by decide) with h504 | h504
              · rcases m.htr 0 3 5 (by decide) (by decide) with h505 | h505
                · rcases m.htr 0 4 5 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h508 | h508
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h509 | h509
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h510 | h510
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h511 | h511
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h512 | h512
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h513 | h513
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h514 | h514
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h515 | h515
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h516 | h516
                                      · linarith only [h501, h513, h516, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · linarith only [h345, h500, h507, h510, h512, h516, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                    · linarith only [h345, h500, h507, h510, h512, h515, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h345, h500, h507, h510, h511, h514, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h521 | h521
                                  · linarith only [h513, h521, hc34, hlam, hphi, u3ehi4]
                                  · linarith only [h345, h500, h507, h510, h511, h521, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h345, h500, h512, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                            · linarith only [h345, h500, h510, h511, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h345, h500, h501, h504, h510, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · linarith only [h0, h500, h509, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h500, h502, h508, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · linarith only [h0, h501, h507, hlam]
                  · linarith only [h345, h500, h506, hlam]
                · linarith only [h504, h505, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h532 | h532
                · linarith only [h504, h532, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h537 | h537
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h538 | h538
                          · linarith only [h504, h535, h538, hc12, hlam, hphi, ht01, u0ehi2]
                          · linarith only [h345, h500, h537, h538, hc34, hlam, hphi, ht23, u2ehi4]
                        · linarith only [h345, h500, h536, h537, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h500, h502, h532, h536, hc02, hlam, hphi, u0ehi2]
                    · linarith only [h0, h501, h532, h535, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h345, h500, h534, hlam]
            · linarith only [h502, h503, hc25, hlam, hphi, u2ehi3]
          · linarith only [h501, h502, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h547 | h547
          · linarith only [h501, h547, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h549 | h549
            · linarith only [h501, h549, hc23, hlam, hphi, u2ehi4]
            · linarith only [h0, h500, h549, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h552 | h552
        · rcases m.htr 0 2 4 (by decide) (by decide) with h553 | h553
          · rcases m.htr 0 2 5 (by decide) (by decide) with h554 | h554
            · rcases m.htr 0 3 4 (by decide) (by decide) with h555 | h555
              · rcases m.htr 0 3 5 (by decide) (by decide) with h556 | h556
                · rcases m.htr 0 4 5 (by decide) (by decide) with h557 | h557
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h558 | h558
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h559 | h559
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h560 | h560
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h561 | h561
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h562 | h562
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h563 | h563
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h564 | h564
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h565 | h565
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h566 | h566
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h567 | h567
                                      · linarith only [h0, h552, h564, h567, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                      · linarith only [h0, h552, h564, h566, h567, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                                      · linarith only [h566, h570, hc34, hlam, hphi, ht23, u2ehi3]
                                      · rcases h5bigk with h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [hlam, p572_0]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h500, hlam, p572_1]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          rcases p572_3 (m.d 0 5) (by simp) with h575 | h575
                                          · rcases p572_3 (m.d 1 5) (by simp) with h576 | h576
                                            · rcases p572_3 (m.d 2 5) (by simp) with h577 | h577
                                              · linarith only [h554, h577, hlam]
                                              · rcases p572_3 (m.d 3 5) (by simp) with h579 | h579
                                                · linarith only [h556, h579, hlam]
                                                · rcases p572_3 (m.d 4 5) (by simp) with h581 | h581
                                                  · linarith only [h557, h581, hlam]
                                                  · linarith only [h566, h581, hlam]
                                            · linarith only [h560, h576, hlam]
                                          · linarith only [h554, h575, hlam]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          rcases p572_3 (m.d 0 5) (by simp) with h586 | h586
                                          · rcases p572_3 (m.d 1 5) (by simp) with h587 | h587
                                            · rcases p572_3 (m.d 2 5) (by simp) with h588 | h588
                                              · linarith only [h554, h588, hlam]
                                              · linarith only [h565, h588, hlam]
                                            · linarith only [h562, h587, hlam]
                                          · linarith only [h556, h586, hlam]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h500, h558, h561, h563, h566, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p572_1, u2ehi3]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h558, h561, h563, hc12, hlam, hphi, ht01, p572_1, u0ehi4]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [hlam, p572_0]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          rcases p572_3 (m.d 0 5) (by simp) with h596 | h596
                                          · linarith only [h500, h596, hlam]
                                          · linarith only [h554, h596, hlam]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          rcases p572_3 (m.d 0 5) (by simp) with h599 | h599
                                          · linarith only [h500, h599, hlam]
                                          · linarith only [h556, h599, hlam]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h558, h561, h563, h566, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p572_1, u2ehi3]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h554, hlam, p572_1]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h560, hlam, p572_1]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [hlam, p572_0]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h0, h554, h570, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p572_1, u3ehi3]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h566, hlam, p572_1]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h556, hlam, p572_0]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h562, hlam, p572_0]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h565, hlam, p572_0]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [hlam, p572_0]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h570, hlam, p572_1]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h557, hlam, p572_0]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h563, hlam, p572_0]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h557, hc04, hlam, hphi, ht0b, ht5b, p572_1, u5ehi2]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [h345, h557, h558, h561, h570, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p572_1, u3ehi3]
                                        · have p572_0 := h572c.1
                                          have p572_1 := h572c.2.1
                                          have p572_2 := h572c.2.2.1
                                          have p572_3 := h572c.2.2.2
                                          linarith only [hlam, p572_0]
                                  · linarith only [h0, h552, h556, h564, h565, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h619 | h619
                                  · linarith only [h564, h619, hc34, hlam, hphi, u3ehi4]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h621 | h621
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h622 | h622
                                      · rcases h5bigk with h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h500, hlam, p623_1]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          rcases p623_3 (m.d 0 5) (by simp) with h626 | h626
                                          · rcases p623_3 (m.d 1 5) (by simp) with h627 | h627
                                            · rcases p623_3 (m.d 2 5) (by simp) with h628 | h628
                                              · linarith only [h554, h628, hlam]
                                              · rcases p623_3 (m.d 3 5) (by simp) with h630 | h630
                                                · linarith only [h556, h630, hlam]
                                                · linarith only [h619, h630, hlam]
                                            · linarith only [h560, h627, hlam]
                                          · linarith only [h554, h626, hlam]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h500, h558, h561, h563, h619, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p623_1, u3ehi2]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          rcases p623_3 (m.d 0 5) (by simp) with h636 | h636
                                          · rcases p623_3 (m.d 1 5) (by simp) with h637 | h637
                                            · rcases p623_3 (m.d 2 5) (by simp) with h638 | h638
                                              · linarith only [h554, h638, hlam]
                                              · linarith only [h621, h638, hlam]
                                            · linarith only [h563, h637, hlam]
                                          · linarith only [h557, h636, hlam]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h558, h561, h563, hc12, hlam, hphi, ht01, p623_1, u0ehi4]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          rcases p623_3 (m.d 0 5) (by simp) with h645 | h645
                                          · linarith only [h500, h645, hlam]
                                          · linarith only [h554, h645, hlam]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h558, h561, h563, h619, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p623_1, u2ehi2]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          rcases p623_3 (m.d 0 5) (by simp) with h649 | h649
                                          · linarith only [h500, h649, hlam]
                                          · linarith only [h557, h649, hlam]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h554, hlam, p623_1]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h560, hlam, p623_1]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h619, hlam, p623_1]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h0, h554, hc12, hlam, hphi, ht01, ht0b, ht5b, p623_1, u5ehi4]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h556, hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h562, hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [hc35, hlam, hphi, ht23, p623_1, u2ehi4]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h0, h552, h555, h622, hc12, hlam, hphi, ht01, ht0b, ht5b, p623_1, u5ehi4]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h557, hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h563, hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h621, hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [h622, hlam, p623_0]
                                        · have p623_0 := h623c.1
                                          have p623_1 := h623c.2.1
                                          have p623_2 := h623c.2.2.1
                                          have p623_3 := h623c.2.2.2
                                          linarith only [hlam, p623_0]
                                      · linarith only [h0, h553, h621, h622, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h668 | h668
                                      · linarith only [h0, h552, h555, h564, h621, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                      · linarith only [h564, h668, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h345, h557, h563, hlam]
                            · linarith only [h345, h561, h562, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                          · linarith only [h345, h552, h555, h561, hc02, hlam, hphi, u0ehi0]
                        · linarith only [h0, h560, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                      · linarith only [h0, h559, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h552, h558, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h677 | h677
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h678 | h678
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h679 | h679
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h680 | h680
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h681 | h681
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h682 | h682
                              · linarith only [h557, h677, h680, h682, hc12, hlam, hphi, ht01, u0ehi3]
                              · linarith only [h345, h682, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
                            · linarith only [h0, h552, h556, h680, h681, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h555, h557, h677, h680, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h554, h679, hlam]
                      · linarith only [h0, h553, h557, h678, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h0, h677, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h555, h556, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h691 | h691
                · linarith only [h555, h691, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h693 | h693
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h694 | h694
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h695 | h695
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h696 | h696
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h697 | h697
                          · linarith only [h555, h697, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h699 | h699
                            · linarith only [h691, h699, hc13, hlam, hphi, ht01, u0ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h701 | h701
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h702 | h702
                                · linarith only [h552, h697, h702, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h704 | h704
                                  · linarith only [h552, h555, h704, hc34, hlam, hphi, u3ehi4]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h706 | h706
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h707 | h707
                                      · rcases h5bigk with h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [hlam, p708_0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h500, hlam, p708_1]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h555, h693, h704, hc34, hlam, hphi, ht23, p708_1, u2ehi2]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h691, hlam, p708_1]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          rcases p708_3 (m.d 0 5) (by simp) with h713 | h713
                                          · rcases p708_3 (m.d 1 5) (by simp) with h714 | h714
                                            · rcases p708_3 (m.d 2 5) (by simp) with h715 | h715
                                              · linarith only [h554, h715, hlam]
                                              · linarith only [h706, h715, hlam]
                                            · linarith only [h701, h714, hlam]
                                          · linarith only [h693, h713, hlam]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h699, hc35, hlam, hphi, ht01, ht12, ht23, p708_1, u0ehi4]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [hlam, p708_0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h699, h704, hc35, hlam, hphi, ht23, p708_1, u2ehi2]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h699, hlam, p708_1]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          rcases p708_3 (m.d 0 5) (by simp) with h724 | h724
                                          · linarith only [h500, h724, hlam]
                                          · linarith only [h693, h724, hlam]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h554, hlam, p708_1]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h696, hlam, p708_1]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [hlam, p708_0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h704, hlam, p708_1]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h554, hc02, hlam, hphi, ht0b, ht5b, p708_1, u5ehi4]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h500, h707, hc34, hlam, hphi, ht01, ht12, ht23, p708_1, u0ehi0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h500, h707, hc34, hlam, hphi, ht01, ht12, ht23, p708_1, u0ehi0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h707, hc34, hlam, hphi, ht23, p708_1, u2ehi4]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [hlam, p708_0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          rcases p708_3 (m.d 0 5) (by simp) with h736 | h736
                                          · linarith only [h691, h736, hlam]
                                          · linarith only [h693, h736, hlam]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h693, hlam, p708_0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h701, hlam, p708_0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h706, hlam, p708_0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [h707, hlam, p708_0]
                                        · have p708_0 := h708c.1
                                          have p708_1 := h708c.2.1
                                          have p708_2 := h708c.2.2.1
                                          have p708_3 := h708c.2.2.2
                                          linarith only [hlam, p708_0]
                                      · linarith only [h345, h697, h706, h707, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                                    · linarith only [h345, h693, h697, h706, hc34, hlam, hphi, ht23, u2ehi3]
                              · linarith only [h345, h693, h701, hc05, hlam, hphi, u0ehi0]
                        · linarith only [h0, h554, h693, h696, hc04, hlam, hphi, u0ehi0]
                      · linarith only [h0, h554, h695, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h553, h694, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h750 | h750
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h751 | h751
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h752 | h752
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h753 | h753
                          · linarith only [h555, h753, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h755 | h755
                            · linarith only [h753, h755, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h757 | h757
                              · linarith only [h693, h751, h757, hc12, hlam, hphi, ht01, u0ehi3]
                              · linarith only [h345, h757, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
                        · linarith only [h0, h752, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                      · linarith only [h0, h553, h751, hc02, hlam, hphi, u0ehi0]
                    · linarith only [h0, h554, h750, hc23, hlam, hphi, u2ehi4]
            · linarith only [h552, h554, hc25, hlam, hphi, u2ehi2]
          · linarith only [h552, h553, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h765 | h765
          · linarith only [h552, h765, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h767 | h767
            · linarith only [h552, h767, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h769 | h769
              · rcases m.htr 0 3 5 (by decide) (by decide) with h770 | h770
                · rcases m.htr 0 4 5 (by decide) (by decide) with h771 | h771
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
                    · linarith only [h552, h772, hc12, hlam, hphi, ht01, u0ehi1]
                    · linarith only [h0, h772, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
                    · linarith only [h0, h552, h775, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h775, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h769, h770, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h779 | h779
                · linarith only [h769, h779, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h782 | h782
                    · linarith only [h0, h552, h782, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h782, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h785 | h785
                    · linarith only [h0, h552, h785, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h785, hc23, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
