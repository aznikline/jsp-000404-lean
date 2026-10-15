import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_I_L_I_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
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
                      · linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
                            · linarith only [h1, h14, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h14, hc34, hlam, hphi, u3ehi1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
                            · linarith only [h1, h17, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h17, hc34, hlam, hphi, u3ehi1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                            · linarith only [h1, h21, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h21, hc34, hlam, hphi, u3ehi1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                            · linarith only [h1, h24, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h24, hc34, hlam, hphi, u3ehi1]
                    · linarith only [h7, h9, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h8, hc35, hlam, hphi, u3ehi0]
                · linarith only [h1, h7, hc34, hlam, hphi, u3ehi1]
              · linarith only [h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h32 | h32
            · rcases m.htr 0 2 5 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
                · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                      · linarith only [h0, h37, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                            · linarith only [h1, h41, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h34, h41, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h33, h4, h40, hc12, hc23, hlam, hphi]
                        · linarith only [h32, h39, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h34, h36, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h35, hc35, hlam, hphi, u3ehi0]
                · linarith only [h34, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h49 | h49
                · rcases m.htr 0 3 5 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h51 | h51
                    · linarith only [h32, h33, h51, hlam]
                    · linarith only [h49, h51, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h49, h50, hc35, hlam, hphi, u3ehi3]
                · linarith only [h49, hc34, hlam, hphi, u3ehi0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h56 | h56
              · rcases m.htr 0 3 4 (by decide) (by decide) with h57 | h57
                · rcases m.htr 0 3 5 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
                      · linarith only [h4, h56, h58, h60, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
                        · linarith only [h32, h56, h58, h62, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                            · linarith only [h1, h65, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h57, h65, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h32, h56, h64, hc12, hc24, hlam, hphi]
                    · linarith only [h32, h56, h58, h59, hc45, hlam, hphi, ht34, u3ehi4]
                  · linarith only [h58, hc35, hlam, hphi, u3ehi0]
                · linarith only [h1, h57, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h72 | h72
                · rcases m.htr 0 3 5 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h74 | h74
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                      · linarith only [h4, h72, h75, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                        · linarith only [h0, h32, h77, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                          · linarith only [h0, h56, h79, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                            · linarith only [h1, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h72, h81, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h72, h74, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h73, hc35, hlam, hphi, u3ehi0]
                · linarith only [h1, h72, hc34, hlam, hphi, u3ehi1]
        · linarith only [h1, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h1, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
      · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
        · rcases m.htr 0 2 3 (by decide) (by decide) with h91 | h91
          · linarith only [h0, h1, h91, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h93 | h93
            · rcases m.htr 0 2 5 (by decide) (by decide) with h94 | h94
              · rcases m.htr 0 3 4 (by decide) (by decide) with h95 | h95
                · rcases m.htr 0 3 5 (by decide) (by decide) with h96 | h96
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h97 | h97
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                      · linarith only [h91, h93, h96, h97, h98, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                            · linarith only [h0, h1, h100, h102, h98, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h102, h95, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h1, h100, h101, h94, h98, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1, h100, h93, h98, hc12, hc23, hlam, hphi]
                    · linarith only [h95, h97, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h96, hc35, hlam, hphi, u3ehi0]
                · linarith only [h95, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
                · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h112 | h112
                    · linarith only [h112, h93, h94, hlam]
                    · linarith only [h110, h112, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h111, hc35, hlam, hphi, u3ehi0]
                · linarith only [h110, hc34, hlam, hphi, u3ehi0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h117 | h117
              · rcases m.htr 0 3 4 (by decide) (by decide) with h118 | h118
                · rcases m.htr 0 3 5 (by decide) (by decide) with h119 | h119
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                      · linarith only [h0, h121, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                        · linarith only [h0, h1, h121, h123, h93, hc02, hc23, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                            · linarith only [h1, h121, h126, h89, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h126, hc34, hlam, hphi, u3ehi0]
                          · linarith only [h1, h117, h121, h125, h89, h93, hc12, hc23, hlam, hphi]
                    · linarith only [h117, h119, h120, h93, hc45, hlam, hphi, ht34, u3ehi4]
                  · linarith only [h118, h119, hc35, hlam, hphi, u3ehi3]
                · linarith only [h118, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h133 | h133
                · rcases m.htr 0 3 5 (by decide) (by decide) with h134 | h134
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
                      · linarith only [h0, h1, h136, h91, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                        · linarith only [h0, h138, h93, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h140 | h140
                          · linarith only [h0, h117, h140, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h142 | h142
                            · linarith only [h1, h136, h142, h89, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h133, h142, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h133, h135, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h133, h134, hc35, hlam, hphi, u3ehi3]
                · linarith only [h133, hc34, hlam, hphi, u3ehi0]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h148 | h148
          · linarith only [h0, h148, h90, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h150 | h150
            · rcases m.htr 0 2 5 (by decide) (by decide) with h151 | h151
              · linarith only [h0, h151, h90, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h153 | h153
                · rcases m.htr 0 3 5 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
                    · linarith only [h155, h89, h90, hlam]
                    · linarith only [h153, h155, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h153, h154, hc35, hlam, hphi, u3ehi3]
                · linarith only [h153, hc34, hlam, hphi, u3ehi0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h160 | h160
              · linarith only [h150, h160, h89, h90, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h162 | h162
                · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                    · linarith only [h164, h89, h90, hlam]
                    · linarith only [h162, h164, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h162, h163, hc35, hlam, hphi, u3ehi3]
                · linarith only [h162, hc34, hlam, hphi, u3ehi0]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h169 | h169
        · rcases m.htr 0 2 3 (by decide) (by decide) with h170 | h170
          · linarith only [h0, h170, h89, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h172 | h172
            · linarith only [h0, h172, h89, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h174 | h174
              · rcases m.htr 0 3 4 (by decide) (by decide) with h175 | h175
                · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                      · linarith only [h0, h170, h178, h89, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                        · linarith only [h0, h1, h172, h174, h176, h178, h180, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                              · linarith only [h0, h178, h182, h183, h184, h89, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h0, h183, h184, h89, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h175, h183, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h0, h174, h180, h182, h89, hc12, hc24, hlam, hphi]
                    · linarith only [h0, h174, h176, h177, h89, hc45, hlam, hphi, ht34, u3ehi4]
                  · linarith only [h175, h176, hc35, hlam, hphi, u3ehi3]
                · linarith only [h175, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
                · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                      · linarith only [h170, h192, h195, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h197 | h197
                        · linarith only [h0, h1, h172, h197, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h199 | h199
                          · linarith only [h0, h174, h199, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h201 | h201
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h202 | h202
                              · linarith only [h169, h195, h201, h202, h89, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h202, hc35, hlam, hphi, u3ehi1]
                            · linarith only [h1, h201, hc34, hlam, hphi, u3ehi0]
                    · linarith only [h169, h193, h194, h89, hc45, hlam, hphi, ht34, u3ehi4]
                  · linarith only [h193, hc35, hlam, hphi, u3ehi0]
                · linarith only [h192, hc34, hlam, hphi, u3ehi0]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h209 | h209
          · linarith only [h0, h209, h89, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h211 | h211
            · linarith only [h0, h211, h89, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h213 | h213
              · linarith only [h0, h169, h213, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h215 | h215
                · rcases m.htr 0 3 5 (by decide) (by decide) with h216 | h216
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h217 | h217
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
                      · linarith only [h0, h209, h218, h89, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h220 | h220
                        · linarith only [h0, h169, h211, h217, h220, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                          · linarith only [h0, h169, h213, h222, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                                      · rcases h0bigk with h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h169, h222, h226, h228, hc02, hc23, hlam, hphi, p230_1]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h1, hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h89, hlam, p230_1]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h169, hlam, p230_1]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h0, hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h209, hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h211, hlam, p230_1]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h213, hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h0, h1, h218, hc12, hc23, hlam, hphi, p230_1]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          rcases p230_3 (m.d 0 1) (by simp) with h242 | h242
                                          · linarith only [h1, h242, hlam]
                                          · linarith only [h0, h242, hlam]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h1, h215, h218, h229, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u3ehi4]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h1, h216, h218, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u3ehi4]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h0, h218, h224, h89, hc12, hc23, hlam, hphi, p230_1]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          rcases p230_3 (m.d 0 1) (by simp) with h249 | h249
                                          · linarith only [h249, h89, hlam]
                                          · linarith only [h0, h249, hlam]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h215, hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h216, h218, h224, h89, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p230_1, u3ehi4]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h0, h169, h222, h226, h228, hc12, hc23, hlam, hphi, p230_1]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          rcases p230_3 (m.d 0 1) (by simp) with h256 | h256
                                          · linarith only [h169, h256, hlam]
                                          · linarith only [h0, h256, hlam]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h216, hlam, p230_0]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [h217, hlam, p230_1]
                                        · have p230_0 := h230c.1
                                          have p230_1 := h230c.2.1
                                          have p230_2 := h230c.2.2.1
                                          have p230_3 := h230c.2.2.2
                                          linarith only [hlam, p230_0]
                                      · linarith only [h229, hc45, hlam, hphi, ht34, u3ehi3]
                                    · linarith only [h0, h211, h217, h218, h224, h228, h89, hc12, hc23, hlam, hphi]
                                  · linarith only [h1, h218, h227, hc35, hlam, hphi, u3ehi0]
                                · linarith only [h1, h215, h218, h226, hlam]
                              · linarith only [h1, h216, h225, hlam]
                            · linarith only [h1, h215, h224, hlam]
                    · linarith only [h215, h217, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h215, h216, hc35, hlam, hphi, u3ehi3]
                · linarith only [h215, hc34, hlam, hphi, u3ehi0]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h271 | h271
    · linarith only [h0, h271, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h273 | h273
      · rcases m.htr 0 1 5 (by decide) (by decide) with h274 | h274
        · rcases m.htr 0 2 3 (by decide) (by decide) with h275 | h275
          · rcases m.htr 0 2 4 (by decide) (by decide) with h276 | h276
            · rcases m.htr 0 2 5 (by decide) (by decide) with h277 | h277
              · rcases m.htr 0 3 4 (by decide) (by decide) with h278 | h278
                · rcases m.htr 0 3 5 (by decide) (by decide) with h279 | h279
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h282 | h282
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h283 | h283
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h284 | h284
                            · linarith only [h271, h273, h281, h284, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h275, h278, h284, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h0, h273, h279, h280, h283, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h271, h273, h279, h280, h281, h282, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h0, h273, h279, h280, h281, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h278, h280, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h278, h279, hc35, hlam, hphi, u3ehi3]
                · linarith only [h278, hc34, hlam, hphi, u3ehi0]
              · linarith only [h275, h277, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h275, h276, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h295 | h295
            · rcases m.htr 0 2 5 (by decide) (by decide) with h296 | h296
              · rcases m.htr 0 3 4 (by decide) (by decide) with h297 | h297
                · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
                      · linarith only [h0, h273, h275, h298, h299, h300, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h0, h273, h298, h299, h300, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h297, h299, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h297, h298, hc35, hlam, hphi, u3ehi3]
                · linarith only [h297, hc34, hlam, hphi, u3ehi0]
              · linarith only [h0, h274, h296, hlam]
            · linarith only [h0, h273, h295, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h308 | h308
          · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
            · rcases m.htr 0 2 5 (by decide) (by decide) with h310 | h310
              · rcases m.htr 0 3 4 (by decide) (by decide) with h311 | h311
                · rcases m.htr 0 3 5 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h313 | h313
                    · linarith only [h273, h274, h313, hlam]
                    · linarith only [h311, h313, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h312, hc35, hlam, hphi, u3ehi0]
                · linarith only [h311, hc34, hlam, hphi, u3ehi0]
              · linarith only [h308, h310, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h308, h309, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h320 | h320
            · rcases m.htr 0 2 5 (by decide) (by decide) with h321 | h321
              · rcases m.htr 0 3 4 (by decide) (by decide) with h322 | h322
                · rcases m.htr 0 3 5 (by decide) (by decide) with h323 | h323
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h324 | h324
                    · linarith only [h273, h274, h324, hlam]
                    · linarith only [h322, h324, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h322, h323, hc35, hlam, hphi, u3ehi3]
                · linarith only [h322, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h329 | h329
                · rcases m.htr 0 3 5 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h0, h273, h321, h331, hlam]
                    · linarith only [h329, h331, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h330, hc35, hlam, hphi, u3ehi0]
                · linarith only [h329, hc34, hlam, hphi, u3ehi0]
            · linarith only [h0, h273, h320, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h337 | h337
        · rcases m.htr 0 2 3 (by decide) (by decide) with h338 | h338
          · rcases m.htr 0 2 4 (by decide) (by decide) with h339 | h339
            · rcases m.htr 0 2 5 (by decide) (by decide) with h340 | h340
              · rcases m.htr 0 3 4 (by decide) (by decide) with h341 | h341
                · rcases m.htr 0 3 5 (by decide) (by decide) with h342 | h342
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h343 | h343
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                              · linarith only [h273, h337, h347, h348, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h348, hc35, hlam, hphi, u3ehi1]
                            · linarith only [h271, h341, h347, hlam]
                          · linarith only [h0, h338, h341, h346, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h271, h337, h339, h342, h344, h345, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h0, h338, h344, hlam]
                    · linarith only [h273, h337, h342, h343, hc45, hlam, hphi, ht34, u3ehi4]
                  · linarith only [h341, h342, hc35, hlam, hphi, u3ehi3]
                · linarith only [h341, hc34, hlam, hphi, u3ehi0]
              · linarith only [h338, h340, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h338, h339, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h360 | h360
            · rcases m.htr 0 2 5 (by decide) (by decide) with h361 | h361
              · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
                · rcases m.htr 0 3 5 (by decide) (by decide) with h363 | h363
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h364 | h364
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
                      · linarith only [h0, h337, h338, h363, h365, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h0, h337, h363, h365, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h273, h337, h363, h364, hc45, hlam, hphi, ht34, u3ehi4]
                  · linarith only [h362, h363, hc35, hlam, hphi, u3ehi3]
                · linarith only [h362, hc34, hlam, hphi, u3ehi0]
              · linarith only [h273, h337, h360, h361, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h372 | h372
              · rcases m.htr 0 3 4 (by decide) (by decide) with h373 | h373
                · rcases m.htr 0 3 5 (by decide) (by decide) with h374 | h374
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h375 | h375
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
                      · linarith only [h0, h337, h338, h374, h376, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h0, h337, h374, h376, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h0, h337, h360, h374, h375, hc45, hlam, hphi, ht34, u3ehi4]
                  · linarith only [h374, hc35, hlam, hphi, u3ehi0]
                · linarith only [h373, hc34, hlam, hphi, u3ehi0]
              · linarith only [h0, h337, h372, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h383 | h383
          · rcases m.htr 0 2 4 (by decide) (by decide) with h384 | h384
            · rcases m.htr 0 2 5 (by decide) (by decide) with h385 | h385
              · rcases m.htr 0 3 4 (by decide) (by decide) with h386 | h386
                · rcases m.htr 0 3 5 (by decide) (by decide) with h387 | h387
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h388 | h388
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h392 | h392
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h393 | h393
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                                · linarith only [h383, h394, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h386, h394, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · linarith only [h271, h387, h393, hlam]
                            · linarith only [h271, h386, h392, hlam]
                          · linarith only [h271, h386, h389, h391, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h384, h390, hlam]
                      · linarith only [h0, h383, h387, h389, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h386, h388, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h387, hc35, hlam, hphi, u3ehi0]
                · linarith only [h383, h386, hc34, hlam, hphi, u3ehi2]
              · linarith only [h383, h385, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h383, h384, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h407 | h407
            · rcases m.htr 0 2 5 (by decide) (by decide) with h408 | h408
              · rcases m.htr 0 3 4 (by decide) (by decide) with h409 | h409
                · rcases m.htr 0 3 5 (by decide) (by decide) with h410 | h410
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h411 | h411
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h412 | h412
                      · linarith only [h383, h409, h412, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h415 | h415
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h416 | h416
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h417 | h417
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h418 | h418
                                · linarith only [h0, h407, h412, h418, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h271, h409, h418, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · linarith only [h271, h417, hc35, hlam, hphi, u3ehi0]
                            · linarith only [h271, h409, h416, hlam]
                          · linarith only [h0, h408, h415, hlam]
                        · linarith only [h0, h407, h414, hlam]
                    · linarith only [h409, h411, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h409, h410, hc35, hlam, hphi, u3ehi3]
                · linarith only [h409, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h428 | h428
                · rcases m.htr 0 3 5 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h430 | h430
                    · linarith only [h407, h408, h430, hlam]
                    · linarith only [h428, h430, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h429, hc35, hlam, hphi, u3ehi0]
                · linarith only [h428, hc34, hlam, hphi, u3ehi0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h435 | h435
              · rcases m.htr 0 3 4 (by decide) (by decide) with h436 | h436
                · rcases m.htr 0 3 5 (by decide) (by decide) with h437 | h437
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h438 | h438
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h439 | h439
                      · linarith only [h383, h436, h439, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h441 | h441
                        · linarith only [h407, h439, h441, hc02, hc23, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h443 | h443
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
                                  · linarith only [h0, h435, h441, h446, h447, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                                  · linarith only [h447, hc35, hlam, hphi, u3ehi2]
                                · linarith only [h337, h436, h437, h439, h443, h446, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h271, h337, h437, h441, h443, h445, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h271, h444, hc34, hlam, hphi, u3ehi0]
                          · linarith only [h0, h435, h443, hlam]
                    · linarith only [h407, h435, h437, h438, hc45, hlam, hphi, ht34, u3ehi4]
                  · linarith only [h437, hc35, hlam, hphi, u3ehi0]
                · linarith only [h436, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h457 | h457
                · rcases m.htr 0 3 5 (by decide) (by decide) with h458 | h458
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
                      · linarith only [h383, h457, h460, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h462 | h462
                        · linarith only [h407, h460, h462, hc02, hc23, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h464 | h464
                          · linarith only [h435, h458, h460, h464, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h466 | h466
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h467 | h467
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h468 | h468
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h469 | h469
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h470 | h470
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h471 | h471
                                      · rcases h0bigk with h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h0, hlam, p472_1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h271, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h273, hlam, p472_1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h337, hlam, p472_1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h0, h464, h468, h470, hc01, hc23, hlam, hphi, ht12, p472_1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h383, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h407, hlam, p472_1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h435, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          rcases p472_3 (m.d 0 1) (by simp) with h483 | h483
                                          · linarith only [h271, h483, hlam]
                                          · rcases p472_3 (m.d 0 2) (by simp) with h485 | h485
                                            · linarith only [h383, h485, hlam]
                                            · linarith only [h0, h485, hlam]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          rcases p472_3 (m.d 0 1) (by simp) with h488 | h488
                                          · linarith only [h271, h488, hlam]
                                          · rcases p472_3 (m.d 0 2) (by simp) with h490 | h490
                                            · linarith only [h383, h490, hlam]
                                            · rcases p472_3 (m.d 0 3) (by simp) with h492 | h492
                                              · rcases p472_3 (m.d 0 4) (by simp) with h493 | h493
                                                · linarith only [h457, h493, hlam]
                                                · linarith only [h407, h493, hlam]
                                              · linarith only [h383, h492, hlam]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h271, h457, h460, h471, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p472_1, u3ehi4]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h271, h458, h460, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p472_1, u3ehi4]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          rcases p472_3 (m.d 0 1) (by simp) with h500 | h500
                                          · linarith only [h273, h500, hlam]
                                          · rcases p472_3 (m.d 0 2) (by simp) with h502 | h502
                                            · linarith only [h407, h502, hlam]
                                            · linarith only [h0, h502, hlam]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          rcases p472_3 (m.d 0 1) (by simp) with h505 | h505
                                          · linarith only [h273, h505, hlam]
                                          · rcases p472_3 (m.d 0 2) (by simp) with h507 | h507
                                            · linarith only [h407, h507, hlam]
                                            · rcases p472_3 (m.d 0 3) (by simp) with h509 | h509
                                              · rcases p472_3 (m.d 0 4) (by simp) with h510 | h510
                                                · rcases p472_3 (m.d 0 5) (by simp) with h511 | h511
                                                  · linarith only [h459, h511, hlam]
                                                  · linarith only [h435, h511, hlam]
                                                · linarith only [h407, h510, hlam]
                                              · linarith only [h383, h509, hlam]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h457, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h458, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p472_1, u3ehi4]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          rcases p472_3 (m.d 0 1) (by simp) with h519 | h519
                                          · linarith only [h337, h519, hlam]
                                          · rcases p472_3 (m.d 0 2) (by simp) with h521 | h521
                                            · linarith only [h435, h521, hlam]
                                            · linarith only [h0, h521, hlam]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          rcases p472_3 (m.d 0 1) (by simp) with h524 | h524
                                          · linarith only [h337, h524, hlam]
                                          · rcases p472_3 (m.d 0 2) (by simp) with h526 | h526
                                            · linarith only [h435, h526, hlam]
                                            · rcases p472_3 (m.d 0 3) (by simp) with h528 | h528
                                              · rcases p472_3 (m.d 0 4) (by simp) with h529 | h529
                                                · rcases p472_3 (m.d 0 5) (by simp) with h530 | h530
                                                  · rcases h2bigk with h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h0, hlam, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h383, hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h407, hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h435, hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h0, h460, hc01, hc23, hlam, hphi, ht12, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h460, hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h462, hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h464, hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      rcases p531_3 (m.d 0 2) (by simp) with h542 | h542
                                                      · linarith only [h542, hlam, p531_0]
                                                      · rcases p531_3 (m.d 1 2) (by simp) with h544 | h544
                                                        · linarith only [h460, h544, hlam]
                                                        · linarith only [h0, h544, hlam]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h0, h407, hc01, hc23, hlam, hphi, ht12, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h0, h337, h464, hc01, hc23, hlam, hphi, ht12, p472_1, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      rcases p531_3 (m.d 0 2) (by simp) with h551 | h551
                                                      · linarith only [h551, hlam, p531_0]
                                                      · rcases p531_3 (m.d 1 2) (by simp) with h553 | h553
                                                        · linarith only [h462, h553, hlam]
                                                        · linarith only [h0, h553, hlam]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h468, hlam, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h0, h337, h464, h468, hc01, hc23, hlam, hphi, ht12, p472_1, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      rcases p531_3 (m.d 0 2) (by simp) with h560 | h560
                                                      · linarith only [h560, hlam, p531_0]
                                                      · rcases p531_3 (m.d 1 2) (by simp) with h562 | h562
                                                        · linarith only [h464, h562, hlam]
                                                        · linarith only [h0, h562, hlam]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h469, hlam, p531_1]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [h470, hlam, p531_0]
                                                    · have p531_0 := h531c.1
                                                      have p531_1 := h531c.2.1
                                                      have p531_2 := h531c.2.2.1
                                                      have p531_3 := h531c.2.2.2
                                                      linarith only [hlam, p531_0]
                                                  · linarith only [h435, h530, hlam]
                                                · linarith only [h407, h529, hlam]
                                              · linarith only [h383, h528, hlam]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h458, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h459, hlam, p472_1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                      · linarith only [h471, hc45, hlam, hphi, ht34, u3ehi3]
                                    · linarith only [h0, h273, h407, h459, h470, hc01, hc14, hlam, hphi]
                                  · linarith only [h271, h460, h469, hc35, hlam, hphi, u3ehi0]
                                · linarith only [h271, h457, h460, h468, hlam]
                              · linarith only [h271, h458, h467, hlam]
                            · linarith only [h271, h457, h466, hlam]
                    · linarith only [h457, h459, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h457, h458, hc35, hlam, hphi, u3ehi3]
                · linarith only [h457, hc34, hlam, hphi, u3ehi0]

theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h10, h13, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h13, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h12, h2, h9, hc24, hlam, hphi, ht45, u5elo0]
                        · linarith only [h11, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h0, h10, h18, h5, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · linarith only [h18, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h9, hc14, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                      · linarith only [h23, h5, h8, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                            · rcases h1bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h25, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 1) (by simp) with h31 | h31
                                · rcases p28_3 (m.d 1 2) (by simp) with h32 | h32
                                  · linarith only [h0, h32, hlam]
                                  · linarith only [h32, h5, hlam]
                                · linarith only [h31, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 1) (by simp) with h36 | h36
                                · rcases p28_3 (m.d 1 2) (by simp) with h37 | h37
                                  · linarith only [h0, h37, hlam]
                                  · linarith only [h37, h6, hlam]
                                · linarith only [h36, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 1) (by simp) with h41 | h41
                                · rcases p28_3 (m.d 1 2) (by simp) with h42 | h42
                                  · linarith only [h0, h42, hlam]
                                  · linarith only [h42, h7, hlam]
                                · linarith only [h41, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h0, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h25, h27, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p28_1, u2elo1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h0, h25, h27, h5, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p28_1, u2elo0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 1) (by simp) with h50 | h50
                                · rcases p28_3 (m.d 1 2) (by simp) with h51 | h51
                                  · rcases p28_3 (m.d 1 3) (by simp) with h52 | h52
                                    · linarith only [h5, h52, hlam]
                                    · linarith only [h0, h25, h27, h5, h52, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p28_1, u2elo0]
                                  · linarith only [h51, h7, hlam]
                                · linarith only [h2, h50, hlam]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h0, h8, hc12, hc34, hlam, hphi, ht23, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h5, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h8, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h25, h27, h3, h4, h7, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p28_1, u2elo0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h1, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h6, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h25, h27, h3, h4, h5, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p28_1, u2elo0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 1) (by simp) with h66 | h66
                                · rcases p28_3 (m.d 1 2) (by simp) with h67 | h67
                                  · rcases p28_3 (m.d 1 3) (by simp) with h68 | h68
                                    · linarith only [h68, h8, hlam]
                                    · linarith only [h25, h27, h5, h68, hc45, hlam, hphi, u5elo1]
                                  · linarith only [h67, h7, hlam]
                                · linarith only [h2, h66, hlam]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h2, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h7, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h2, h25, h27, h5, hc45, hlam, hphi, p28_1, u5elo0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h22, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                            · linarith only [h27, h8, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h23, h26, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h25, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h22, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h3, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
              · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                          · linarith only [h5, h84, h90, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · linarith only [h90, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h5, h89, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h4, h5, h84, h88, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h87, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h5, h84, h86, hlam]
                · linarith only [h84, h85, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h3, h84, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
            · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                  · linarith only [h1, h102, h4, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                      · linarith only [h102, h105, h99, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                            · rcases h1bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h100, h105, h107, h109, hc01, hc45, hlam, hphi, ht0b, ht5b, p110_1]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h113 | h113
                                · rcases p110_3 (m.d 1 2) (by simp) with h114 | h114
                                  · linarith only [h0, h114, hlam]
                                  · linarith only [h114, h99, hlam]
                                · linarith only [h113, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h118 | h118
                                · rcases p110_3 (m.d 1 2) (by simp) with h119 | h119
                                  · linarith only [h0, h119, hlam]
                                  · linarith only [h100, h119, hlam]
                                · linarith only [h118, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h123 | h123
                                · rcases p110_3 (m.d 1 2) (by simp) with h124 | h124
                                  · linarith only [h0, h124, hlam]
                                  · linarith only [h101, h124, hlam]
                                · linarith only [h123, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h0, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h107, h109, h99, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo1]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h0, h100, h105, h107, h109, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h132 | h132
                                · rcases p110_3 (m.d 1 2) (by simp) with h133 | h133
                                  · rcases p110_3 (m.d 1 3) (by simp) with h134 | h134
                                    · linarith only [h134, h99, hlam]
                                    · linarith only [h0, h107, h109, h134, h99, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                                  · linarith only [h101, h133, hlam]
                                · linarith only [h132, h2, hlam]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h102, hc01, hc34, hlam, hphi, ht12, ht23, p110_1]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h99, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h102, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h143 | h143
                                · rcases p110_3 (m.d 1 2) (by simp) with h144 | h144
                                  · rcases p110_3 (m.d 1 3) (by simp) with h145 | h145
                                    · rcases p110_3 (m.d 1 4) (by simp) with h146 | h146
                                      · rcases p110_3 (m.d 1 5) (by simp) with h147 | h147
                                        · linarith only [h147, hlam, p110_0]
                                        · rcases h1emin with h149 | h149 | h149 | h149 | h149
                                          · rcases h4bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h101, h102, h107, h109, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, p150_1, u2elo0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h105, h107, h109, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p150_1, u2elo0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h4, hlam, p150_1]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              rcases p150_3 (m.d 0 4) (by simp) with h155 | h155
                                              · rcases p150_3 (m.d 1 4) (by simp) with h156 | h156
                                                · linarith only [h1, h156, hlam]
                                                · linarith only [h104, h156, hlam]
                                              · linarith only [h155, hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h1, hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h1, h105, h107, h109, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h102, hlam, p150_1]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              rcases p150_3 (m.d 0 4) (by simp) with h164 | h164
                                              · rcases p150_3 (m.d 1 4) (by simp) with h165 | h165
                                                · rcases p150_3 (m.d 2 4) (by simp) with h166 | h166
                                                  · linarith only [h100, h166, hlam]
                                                  · linarith only [h108, h166, hlam]
                                                · linarith only [h165, hlam, p150_0]
                                              · linarith only [h105, h107, h109, h164, h3, hlam]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h3, hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h100, hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h105, hlam, p150_1]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p150_1, u2elo0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h1, h102, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p110_1, p150_1]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h101, h102, h107, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p110_1, p150_1]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              rcases p150_3 (m.d 0 4) (by simp) with h178 | h178
                                              · linarith only [h178, h4, hlam]
                                              · linarith only [h178, h3, hlam]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h101, h102, h107, h109, hlam, p110_1, p150_2]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h1, h101, h102, h107, h109, hlam, p110_1, p150_1]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h104, hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h108, hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [h109, hlam, p150_0]
                                            · have p150_0 := h150c.1
                                              have p150_1 := h150c.2.1
                                              have p150_2 := h150c.2.2.1
                                              have p150_3 := h150c.2.2.2
                                              linarith only [hlam, p150_0]
                                          · linarith only [h0, h149, hlam, ht12, u2elo0]
                                          · linarith only [h102, h149, hc34, hlam, ht12, ht23]
                                          · linarith only [h1, h149, h3, hlam, ht12, u2elo0]
                                          · linarith only [h149, hlam, ht12, ht23, ht34, ht45, u5elo1]
                                      · linarith only [h104, h146, hlam]
                                    · linarith only [h145, hlam, p110_0]
                                  · linarith only [h101, h144, hlam]
                                · linarith only [h143, h2, hlam]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h1, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h100, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h1, h107, h109, h3, h99, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                rcases p110_3 (m.d 0 1) (by simp) with h200 | h200
                                · rcases p110_3 (m.d 1 2) (by simp) with h201 | h201
                                  · rcases p110_3 (m.d 1 3) (by simp) with h202 | h202
                                    · linarith only [h102, h202, hlam]
                                    · linarith only [h1, h107, h109, h202, h3, h99, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1, u2elo0]
                                  · linarith only [h101, h201, hlam]
                                · linarith only [h2, h200, hlam]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h2, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h101, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h107, h109, h99, hc45, hlam, hphi, p110_1, u5elo1]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [h104, hlam, p110_0]
                              · have p110_0 := h110c.1
                                have p110_1 := h110c.2.1
                                have p110_2 := h110c.2.2.1
                                have p110_3 := h110c.2.2.2
                                linarith only [hlam, p110_0]
                            · linarith only [h109, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h104, h108, h2, hc24, hlam, hphi, ht45, u5elo0]
                        · linarith only [h107, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h104, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h101, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h100, h3, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
              · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
                · rcases m.htr 1 3 4 (by decide) (by decide) with h220 | h220
                  · linarith only [h1, h220, h4, hlam]
                  · linarith only [h218, h220, h99, hlam]
                · linarith only [h219, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h218, h3, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h225 | h225
          · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
            · rcases m.htr 1 2 4 (by decide) (by decide) with h227 | h227
              · linarith only [h0, h227, h3, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h229 | h229
                · rcases m.htr 1 3 4 (by decide) (by decide) with h230 | h230
                  · linarith only [h226, h227, h230, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                      · linarith only [h226, h227, h230, h233, hlam]
                      · linarith only [h225, h233, h3, hlam]
                    · linarith only [h226, h227, h232, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h226, h229, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h238 | h238
              · linarith only [h226, h238, h3, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
                · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h243 | h243
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h246 | h246
                            · rcases h1bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                rcases p247_3 (m.d 0 1) (by simp) with h249 | h249
                                · rcases p247_3 (m.d 1 2) (by simp) with h250 | h250
                                  · linarith only [h250, hlam, p247_0]
                                  · rcases p247_3 (m.d 1 3) (by simp) with h252 | h252
                                    · linarith only [h226, h240, h244, h246, h252, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p247_1, u2elo2]
                                    · linarith only [h226, h252, hlam]
                                · linarith only [h249, hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h241, h246, hc01, hc45, hlam, hphi, ht0b, ht5b, p247_1]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                rcases p247_3 (m.d 0 1) (by simp) with h257 | h257
                                · rcases p247_3 (m.d 1 2) (by simp) with h258 | h258
                                  · linarith only [h0, h258, hlam]
                                  · rcases p247_3 (m.d 1 3) (by simp) with h260 | h260
                                    · linarith only [h226, h238, h240, h244, h246, h260, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p247_1, u2elo2]
                                    · linarith only [h241, h260, hlam]
                                · linarith only [h257, hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                rcases p247_3 (m.d 0 1) (by simp) with h264 | h264
                                · rcases p247_3 (m.d 1 2) (by simp) with h265 | h265
                                  · linarith only [h0, h265, hlam]
                                  · linarith only [h240, h265, hlam]
                                · linarith only [h264, hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h0, hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h226, hlam, p247_1]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h238, hlam, p247_1]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h0, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p247_1, u2elo3]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h226, hc01, hlam, hphi, ht12, p247_1, u2elo2]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h226, hc12, hlam, hphi, p247_1, u2elo2]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h226, h238, h240, h244, h246, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p247_1, u2elo2]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                rcases p247_3 (m.d 0 1) (by simp) with h278 | h278
                                · rcases p247_3 (m.d 1 2) (by simp) with h279 | h279
                                  · linarith only [h226, h279, hlam]
                                  · linarith only [h240, h279, hlam]
                                · linarith only [h2, h278, hlam]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h1, hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h1, h240, h244, h246, hc01, hc45, hlam, hphi, ht0b, ht5b, p247_1]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h241, hlam, p247_1]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                rcases p247_3 (m.d 0 1) (by simp) with h287 | h287
                                · rcases p247_3 (m.d 1 2) (by simp) with h288 | h288
                                  · linarith only [h238, h288, hlam]
                                  · linarith only [h240, h288, hlam]
                                · linarith only [h2, h287, hlam]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h2, hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h240, hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [hc13, hlam, hphi, ht34, ht45, p247_1, u5elo1]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [h242, hlam, p247_0]
                              · have p247_0 := h247c.1
                                have p247_1 := h247c.2.1
                                have p247_2 := h247c.2.2.1
                                have p247_3 := h247c.2.2.2
                                linarith only [hlam, p247_0]
                            · linarith only [h246, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h2, h242, h245, h3, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h0, h240, h243, h244, h3, hc25, hlam, hphi, u5elo3]
                      · linarith only [h225, h226, h240, h243, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h242, hc14, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h302 | h302
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                      · linarith only [h226, h240, h241, h303, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · linarith only [h225, h226, h240, h3, h303, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h226, h240, h241, h302, hc25, hlam, hphi, u5elo4]
                · linarith only [h240, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h308 | h308
            · rcases m.htr 1 2 4 (by decide) (by decide) with h309 | h309
              · linarith only [h0, h3, h309, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
                · rcases m.htr 1 3 4 (by decide) (by decide) with h312 | h312
                  · linarith only [h1, h225, h308, h309, h312, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h314 | h314
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                      · linarith only [h0, h3, h308, h312, h315, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h317 | h317
                        · linarith only [h0, h3, h308, h317, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · linarith only [h317, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h309, h314, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h308, h311, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
              · linarith only [h0, h3, h322, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                · rcases m.htr 1 3 4 (by decide) (by decide) with h325 | h325
                  · linarith only [h1, h225, h325, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h327 | h327
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h328 | h328
                      · linarith only [h308, h325, h328, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h330 | h330
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h331 | h331
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                            · rcases h1bigk with h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                rcases p333_3 (m.d 0 1) (by simp) with h335 | h335
                                · rcases p333_3 (m.d 1 2) (by simp) with h336 | h336
                                  · linarith only [h336, hlam, p333_0]
                                  · rcases p333_3 (m.d 1 3) (by simp) with h338 | h338
                                    · linarith only [h1, h325, h338, hlam]
                                    · linarith only [h308, h338, hlam]
                                · linarith only [h335, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                rcases p333_3 (m.d 0 1) (by simp) with h342 | h342
                                · rcases p333_3 (m.d 1 2) (by simp) with h343 | h343
                                  · linarith only [h0, h343, hlam]
                                  · rcases p333_3 (m.d 1 3) (by simp) with h345 | h345
                                    · linarith only [h345, hlam, p333_0]
                                    · rcases p333_3 (m.d 1 4) (by simp) with h347 | h347
                                      · linarith only [h1, h347, hlam]
                                      · linarith only [h325, h347, hlam]
                                · linarith only [h342, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                rcases p333_3 (m.d 0 1) (by simp) with h351 | h351
                                · rcases p333_3 (m.d 1 2) (by simp) with h352 | h352
                                  · linarith only [h0, h352, hlam]
                                  · rcases p333_3 (m.d 1 3) (by simp) with h354 | h354
                                    · linarith only [h325, h354, hlam, p333_1]
                                    · rcases p333_3 (m.d 1 4) (by simp) with h356 | h356
                                      · linarith only [h356, hlam, p333_0]
                                      · rcases p333_3 (m.d 1 5) (by simp) with h358 | h358
                                        · linarith only [h2, h358, hlam]
                                        · rcases h1emin with h360 | h360 | h360 | h360 | h360
                                          · rcases h4bigk with h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [hlam, p361_0]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h3, h308, h324, h325, h330, h332, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p361_1, u2elo3]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h3, hlam, p361_1]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h225, hlam, p361_1]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              rcases p361_3 (m.d 0 4) (by simp) with h366 | h366
                                              · rcases p361_3 (m.d 1 4) (by simp) with h367 | h367
                                                · linarith only [h1, h367, hlam]
                                                · linarith only [h327, h367, hlam]
                                              · linarith only [h366, hlam, p361_0]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h1, hlam, p361_0]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [hlam, p361_0]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h322, hlam, p361_1]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h325, hlam, p361_1]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p333_1, p361_1]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h0, h3, h324, h330, h332, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p361_1, u2elo3]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h322, h324, h330, h332, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p361_1, u2elo3]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [hlam, p361_0]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h328, hlam, p361_1]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              rcases p361_3 (m.d 0 4) (by simp) with h380 | h380
                                              · linarith only [h3, h380, hlam]
                                              · linarith only [h1, h308, h324, h325, h330, h332, h380, hlam]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              rcases p361_3 (m.d 0 4) (by simp) with h383 | h383
                                              · linarith only [h225, h383, hlam]
                                              · rcases p361_3 (m.d 1 4) (by simp) with h385 | h385
                                                · linarith only [h325, h385, hlam]
                                                · rcases p361_3 (m.d 2 4) (by simp) with h387 | h387
                                                  · linarith only [h328, h387, hlam]
                                                  · linarith only [h3, h387, hlam]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              rcases p361_3 (m.d 0 4) (by simp) with h390 | h390
                                              · linarith only [h225, h390, hlam]
                                              · linarith only [h1, h390, hlam]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h0, h3, h324, h330, h332, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p361_1]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [hlam, p361_0]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h308, h324, h328, h330, h332, hlam, p361_2]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h1, h308, h324, h325, h330, h332, hlam, p361_1]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h327, hlam, p361_0]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h331, hlam, p361_0]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [h332, hlam, p361_0]
                                            · have p361_0 := h361c.1
                                              have p361_1 := h361c.2.1
                                              have p361_2 := h361c.2.2.1
                                              have p361_3 := h361c.2.2.2
                                              linarith only [hlam, p361_0]
                                          · linarith only [h308, h360, hlam, ht12, u2elo2]
                                          · linarith only [h0, h3, h324, h325, h330, h332, h360, hc01, hc45, hlam, hphi, ht0b, ht12, ht5b, p333_1, u2elo3]
                                          · linarith only [h0, h3, h324, h330, h332, h360, hc01, hc45, hlam, hphi, ht0b, ht12, ht5b, p333_1, u2elo3]
                                          · linarith only [h0, h2, h3, h324, h330, h332, h360, hc45, hlam, hphi, ht12, u2elo3, u5elo0]
                                · linarith only [h351, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                rcases p333_3 (m.d 0 1) (by simp) with h406 | h406
                                · rcases p333_3 (m.d 1 2) (by simp) with h407 | h407
                                  · linarith only [h0, h407, hlam]
                                  · linarith only [h324, h407, hlam]
                                · linarith only [h406, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h0, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h308, hlam, p333_1]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h322, hlam, p333_1]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h0, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p333_1, u2elo3]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h0, h1, h324, h325, hc04, hc25, hlam, hphi, ht0b, ht5b, p333_1]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h1, h3, h324, h325, h330, h332, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p333_1, u2elo3]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h325, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                rcases p333_3 (m.d 0 1) (by simp) with h420 | h420
                                · rcases p333_3 (m.d 1 2) (by simp) with h421 | h421
                                  · linarith only [h308, h421, hlam]
                                  · linarith only [h324, h421, hlam]
                                · linarith only [h2, h420, hlam]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h1, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h1, h3, h324, h330, h332, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p333_1, u2elo3]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h1, h3, h308, h324, h330, h332, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p333_1, u2elo3]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                rcases p333_3 (m.d 0 1) (by simp) with h429 | h429
                                · rcases p333_3 (m.d 1 2) (by simp) with h430 | h430
                                  · linarith only [h322, h430, hlam]
                                  · linarith only [h324, h430, hlam]
                                · linarith only [h2, h429, hlam]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h2, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h324, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h308, h324, h330, h332, hc45, hlam, hphi, p333_1, u5elo1]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [h327, hlam, p333_0]
                              · have p333_0 := h333c.1
                                have p333_1 := h333c.2.1
                                have p333_2 := h333c.2.2.1
                                have p333_3 := h333c.2.2.2
                                linarith only [hlam, p333_0]
                            · linarith only [h328, h332, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h2, h3, h327, h331, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h308, h324, h330, hc25, hlam, hphi, u5elo3]
                    · linarith only [h327, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h324, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h445 | h445
      · rcases m.htr 0 2 4 (by decide) (by decide) with h446 | h446
        · linarith only [h0, h1, h446, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h448 | h448
          · rcases m.htr 1 2 3 (by decide) (by decide) with h449 | h449
            · rcases m.htr 1 2 4 (by decide) (by decide) with h450 | h450
              · linarith only [h0, h1, h446, h450, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h449, h450, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h453 | h453
              · linarith only [h0, h1, h446, h453, hlam]
              · linarith only [h0, h1, h453, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h456 | h456
            · rcases m.htr 1 2 4 (by decide) (by decide) with h457 | h457
              · linarith only [h0, h446, h457, hlam]
              · linarith only [h0, h1, h456, h457, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
              · linarith only [h0, h446, h460, hlam]
              · linarith only [h0, h1, h460, hc12, hlam, hphi, u2elo3]
      · linarith only [h0, h445, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h464 | h464
    · rcases m.htr 0 1 5 (by decide) (by decide) with h465 | h465
      · rcases m.htr 0 2 4 (by decide) (by decide) with h466 | h466
        · rcases m.htr 0 3 4 (by decide) (by decide) with h467 | h467
          · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
            · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
              · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h472 | h472
                    · linarith only [h0, h464, h472, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h472, hc14, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h475 | h475
                    · linarith only [h0, h464, h475, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h475, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h0, h470, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h464, h469, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
            · linarith only [h0, h464, h468, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h481 | h481
            · rcases m.htr 1 2 4 (by decide) (by decide) with h482 | h482
              · rcases m.htr 1 2 5 (by decide) (by decide) with h483 | h483
                · rcases m.htr 1 3 4 (by decide) (by decide) with h484 | h484
                  · linarith only [h0, h464, h467, h484, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h486 | h486
                    · linarith only [h0, h464, h486, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h484, h486, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h483, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h464, h482, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
            · linarith only [h0, h464, h481, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
        · linarith only [h0, h464, h466, hlam]
      · linarith only [h464, h465, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h494 | h494
      · rcases m.htr 0 2 4 (by decide) (by decide) with h495 | h495
        · rcases m.htr 0 3 4 (by decide) (by decide) with h496 | h496
          · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
            · rcases m.htr 1 2 4 (by decide) (by decide) with h498 | h498
              · rcases m.htr 1 2 5 (by decide) (by decide) with h499 | h499
                · rcases m.htr 1 3 4 (by decide) (by decide) with h500 | h500
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h501 | h501
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h502 | h502
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h503 | h503
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h504 | h504
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h505 | h505
                            · linarith only [h497, h502, h505, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h495, h504, h505, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · linarith only [h501, h504, hc24, hlam, hphi, ht45, u5elo1]
                        · linarith only [h503, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h510 | h510
                        · linarith only [h497, h500, h502, h510, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h510, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h464, h501, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h464, h496, h500, hlam]
                · linarith only [h0, h499, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h498, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h494, h497, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h518 | h518
            · rcases m.htr 1 2 4 (by decide) (by decide) with h519 | h519
              · rcases m.htr 1 2 5 (by decide) (by decide) with h520 | h520
                · rcases m.htr 1 3 4 (by decide) (by decide) with h521 | h521
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h522 | h522
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                      · linarith only [h464, h494, h496, h518, h520, h523, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h525 | h525
                        · linarith only [h518, h521, h523, h525, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h525, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h522, hc14, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
                      · linarith only [h464, h494, h520, h521, h530, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h532 | h532
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h534 | h534
                            · rcases h1bigk with h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h0, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h464, h521, hc13, hc34, hlam, hphi, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h464, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h464, h519, h520, h532, h534, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p535_1, u2elo1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, p535_1, u2elo1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h518, h532, h534, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p535_1, u2elo1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h464, h494, h520, h532, h534, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p535_1, u2elo1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                rcases p535_3 (m.d 0 1) (by simp) with h545 | h545
                                · linarith only [h0, h545, hlam]
                                · linarith only [h494, h545, hlam]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h494, h518, h520, h532, h534, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p535_1, u2elo1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h518, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h521, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                rcases p535_3 (m.d 0 1) (by simp) with h552 | h552
                                · linarith only [h0, h520, h532, h534, h552, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p535_1, u2elo1]
                                · linarith only [h494, h552, hlam]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h519, hc01, hlam, hphi, ht12, p535_1, u2elo1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h519, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h518, h519, h532, h534, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p535_1, u2elo1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                rcases p535_3 (m.d 0 1) (by simp) with h559 | h559
                                · linarith only [h464, h559, hlam]
                                · linarith only [h494, h559, hlam]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h494, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h520, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h494, h518, h532, h534, hc01, hc45, hlam, hphi, ht0b, ht5b, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h529, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                            · linarith only [h496, h534, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h464, h494, h519, h529, h530, h533, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h532, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h464, h529, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h464, h494, h519, h520, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
              · linarith only [h0, h494, h519, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
            · linarith only [h0, h494, h518, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h574 | h574
          · rcases m.htr 1 2 3 (by decide) (by decide) with h575 | h575
            · rcases m.htr 1 2 4 (by decide) (by decide) with h576 | h576
              · linarith only [h495, h576, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h494, h576, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
            · linarith only [h0, h494, h575, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h580 | h580
            · rcases m.htr 1 2 4 (by decide) (by decide) with h581 | h581
              · linarith only [h0, h494, h495, h581, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h494, h581, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
            · linarith only [h0, h494, h580, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
      · linarith only [h494, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

end R2N4
