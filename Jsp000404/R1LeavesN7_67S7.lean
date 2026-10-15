import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_H_I_L_R_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
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
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h10, h15, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h10, h13, h15, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                              · linarith only [h0, h10, h18, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h10, h13, h18, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                              · linarith only [h0, h10, h13, h22, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                                · linarith only [h0, h11, h24, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h2, h21, h24, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                              · linarith only [h0, h10, h27, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                                · linarith only [h0, h21, h29, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                                  · linarith only [h0, h10, h13, h21, h31, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · linarith only [h10, h13, h31, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                      · linarith only [h10, h36, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                        · linarith only [h0, h10, h38, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                                  · linarith only [h1, h40, h44, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h2, h41, h44, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h36, h41, h43, hlam]
                              · linarith only [h0, h10, h4, h42, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                                · linarith only [h36, h41, h49, h50, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h36, h4, h50, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h0, h4, h40, h41, h49, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                              · linarith only [h0, h10, h4, h40, h55, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h0, h10, h4, h55, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                              · linarith only [h10, h40, h58, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h10, h4, h58, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                            · linarith only [h2, h65, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                              · linarith only [h0, h61, h67, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h1, h64, h67, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h61, h64, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h6, h61, h63, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h61, h62, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                      · linarith only [h61, h73, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h5, h73, h9, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
                  · linarith only [h7, h76, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                            · linarith only [h2, h76, h82, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                              · linarith only [h0, h78, h84, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h1, h8, h81, h84, hc23, hc35, hlam, hphi]
                          · linarith only [h7, h8, h81, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h6, h78, h80, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h78, h79, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h4, h78, h8, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
                · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                          · linarith only [h1, h7, h91, h96, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                              · linarith only [h3, h7, h91, h95, h99, hc23, hlam, hphi, u2ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h101 | h101
                                · linarith only [h0, h101, h94, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h101, h2, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h7, h91, h92, h94, h98, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h6, h7, h91, h95, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h93, h94, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h4, h7, h93, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h7, h91, h92, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h109 | h109
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h111 | h111
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                          · linarith only [h1, h113, h7, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                              · linarith only [h1, h110, h116, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h118 | h118
                                · linarith only [h0, h111, h118, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h115, h118, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h109, h111, h115, h7, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h110, h112, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h110, h111, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h110, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
                          · linarith only [h1, h109, h128, h7, hc45, hlam, hphi, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                            · linarith only [h109, h130, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                              · linarith only [h1, h125, h132, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                                · linarith only [h109, h126, h134, h2, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h136 | h136
                                  · linarith only [h1, h109, h125, h136, h7, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h1, h125, h136, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h125, h127, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h125, h126, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h125, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
          · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h144 | h144
          · linarith only [h144, h4, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h146 | h146
            · linarith only [h146, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h148 | h148
              · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
                · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                    · linarith only [h0, h151, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h153 | h153
                      · linarith only [h0, h144, h153, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
                        · linarith only [h0, h146, h155, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                                  · linarith only [h1, h157, h161, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h158, h161, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h1, h144, h157, h158, h160, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · linarith only [h0, h159, h4, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h148, h150, h153, h158, h4, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h148, h151, h157, h4, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                    · linarith only [h0, h144, h168, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
                      · linarith only [h0, h170, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                        · linarith only [h0, h146, h172, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                            · linarith only [h150, h175, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                                · linarith only [h144, h150, h177, h178, hc23, hlam, hphi, u2ehi0]
                                · linarith only [h0, h144, h178, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h1, h174, h177, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h148, h168, h174, h4, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h183 | h183
                  · linarith only [h148, h149, h183, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h185 | h185
                    · linarith only [h0, h144, h185, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h187 | h187
                      · linarith only [h0, h187, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                        · linarith only [h0, h146, h189, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h192 | h192
                            · linarith only [h183, h192, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                                · linarith only [h144, h183, h194, h195, hc23, hlam, hphi, u2ehi0]
                                · linarith only [h0, h1, h144, h149, h191, h195, hc35, hc45, hlam, hphi, ht23, u2ehi1, u4ehi3]
                              · linarith only [h1, h149, h191, h194, hc23, hc35, hlam, hphi]
                          · linarith only [h148, h149, h191, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h200 | h200
                · rcases m.htr 0 4 5 (by decide) (by decide) with h201 | h201
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                    · linarith only [h0, h202, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
                      · linarith only [h0, h144, h204, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                        · linarith only [h0, h146, h206, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                          · linarith only [h1, h148, h200, h208, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
                              · linarith only [h0, h146, h148, h200, h211, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h211, h4, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h148, h200, h201, h204, h210, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h148, h200, h201, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                    · linarith only [h0, h217, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                      · linarith only [h0, h219, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                        · linarith only [h0, h146, h221, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                          · linarith only [h1, h148, h223, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                              · linarith only [h148, h226, h4, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h0, h226, h4, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h148, h216, h219, h225, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
                    · linarith only [h0, h230, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h232 | h232
                      · linarith only [h0, h232, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                        · linarith only [h0, h146, h234, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                          · linarith only [h1, h148, h216, h236, hc45, hlam, hphi, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                            · linarith only [h148, h2, h216, h238, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                              · linarith only [h0, h148, h240, h4, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h240, h4, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h243 | h243
        · rcases m.htr 0 2 4 (by decide) (by decide) with h244 | h244
          · rcases m.htr 0 2 5 (by decide) (by decide) with h245 | h245
            · linarith only [h0, h245, h3, hlam]
            · linarith only [h244, h245, hc25, hlam, hphi, u2ehi3]
          · linarith only [h243, h244, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h249 | h249
          · linarith only [h243, h249, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h251 | h251
            · linarith only [h243, h251, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h253 | h253
              · rcases m.htr 0 3 5 (by decide) (by decide) with h254 | h254
                · linarith only [h1, h254, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h256 | h256
                  · linarith only [h0, h253, h254, h256, h3, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                    · linarith only [h0, h249, h253, h254, h258, hc35, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h260 | h260
                      · linarith only [h0, h249, h260, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h1, h251, h258, h262, h3, hlam]
                        · linarith only [h1, h258, h262, h3, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h265 | h265
                · linarith only [h0, h253, h265, h3, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
                  · linarith only [h2, h267, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                    · linarith only [h0, h243, h269, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
                      · linarith only [h0, h249, h271, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h273 | h273
                        · linarith only [h1, h269, h273, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · linarith only [h1, h269, h273, h3, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h276 | h276
      · rcases m.htr 0 2 3 (by decide) (by decide) with h277 | h277
        · rcases m.htr 0 2 4 (by decide) (by decide) with h278 | h278
          · linarith only [h0, h2, h278, hlam]
          · linarith only [h277, h278, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h281 | h281
          · linarith only [h277, h281, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h283 | h283
            · linarith only [h277, h283, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h285 | h285
              · linarith only [h1, h2, h285, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h287 | h287
                · rcases m.htr 0 4 5 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h289 | h289
                    · linarith only [h0, h2, h277, h289, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
                      · linarith only [h0, h277, h291, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h1, h2, h289, h291, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h288, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                    · linarith only [h0, h2, h296, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                      · linarith only [h1, h2, h296, h298, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h1, h2, h296, h298, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h295, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h302 | h302
        · rcases m.htr 0 2 4 (by decide) (by decide) with h303 | h303
          · linarith only [h0, h2, h303, hlam]
          · linarith only [h302, h303, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h306 | h306
          · linarith only [h302, h306, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h308 | h308
            · linarith only [h302, h308, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h310 | h310
              · linarith only [h1, h2, h310, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h312 | h312
                · linarith only [h0, h276, h310, h312, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h314 | h314
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h315 | h315
                    · linarith only [h0, h2, h315, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
                      · linarith only [h1, h2, h306, h315, h317, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h0, h2, h317, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h314, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h321 | h321
    · rcases m.htr 0 1 5 (by decide) (by decide) with h322 | h322
      · rcases m.htr 0 2 3 (by decide) (by decide) with h323 | h323
        · linarith only [h0, h1, h323, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h325 | h325
          · linarith only [h323, h325, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h327 | h327
            · linarith only [h323, h327, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h329 | h329
              · rcases m.htr 0 3 5 (by decide) (by decide) with h330 | h330
                · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                    · linarith only [h0, h1, h332, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h332, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h335 | h335
                    · linarith only [h0, h1, h335, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h335, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h330, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h329, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h340 | h340
        · linarith only [h0, h1, h340, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h342 | h342
          · linarith only [h340, h342, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h344 | h344
            · linarith only [h342, h344, hc24, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h346 | h346
              · rcases m.htr 0 3 5 (by decide) (by decide) with h347 | h347
                · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
                  · linarith only [h321, h322, h348, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
                    · linarith only [h0, h1, h350, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h350, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h347, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h346, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h355 | h355
      · rcases m.htr 0 2 3 (by decide) (by decide) with h356 | h356
        · linarith only [h0, h1, h356, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h358 | h358
          · linarith only [h356, h358, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h360 | h360
            · linarith only [h356, h360, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
              · rcases m.htr 0 3 5 (by decide) (by decide) with h363 | h363
                · rcases m.htr 0 4 5 (by decide) (by decide) with h364 | h364
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
                    · linarith only [h0, h1, h356, h365, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h365, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h321, h364, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h321, h362, h363, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h362, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h371 | h371
        · linarith only [h0, h1, h371, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h373 | h373
          · linarith only [h371, h373, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h375 | h375
            · linarith only [h371, h375, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h377 | h377
              · rcases m.htr 0 3 5 (by decide) (by decide) with h378 | h378
                · rcases m.htr 0 4 5 (by decide) (by decide) with h379 | h379
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h380 | h380
                    · linarith only [h0, h1, h371, h380, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h380, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h321, h379, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h321, h377, h378, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h377, hc34, hlam, hphi, ht23, u2ehi1]

end R2N4
