import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3356000 in
set_option maxHeartbeats 3356000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_H_R_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h10, h11, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h10, h14, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h10, h16, h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                          · linarith only [h0, h10, h18, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h2, h20, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                              · linarith only [h0, h10, h22, h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                                · linarith only [h0, h10, h18, h22, h24, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                                  · linarith only [h0, h22, h26, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h10, h26, h9, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h0, h29, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                      · linarith only [h0, h31, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h1, h34, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h33, h34, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                          · linarith only [h33, h37, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                            · linarith only [h2, h39, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                                · linarith only [h0, h37, h4, h42, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                · linarith only [h33, h41, h42, h9, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                                · linarith only [h0, h4, h45, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                                  · linarith only [h0, h4, h41, h47, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                                    · linarith only [h0, h4, h47, h49, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                    · linarith only [h41, h49, h9, hc12, hc45, hlam, hphi, ht23, ht34]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h54 | h54
                      · linarith only [h0, h54, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h53, h54, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h5, h52, h53, h7, h8, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                    · linarith only [h0, h4, h52, h58, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                      · linarith only [h5, h58, h60, h7, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                          · linarith only [h1, h63, h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                            · linarith only [h2, h65, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                                · linarith only [h4, h68, h8, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                                  · linarith only [h0, h5, h65, h70, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                                    · linarith only [h4, h52, h62, h70, h72, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                                    · linarith only [h4, h52, h62, h72, h8, hc45, hlam, hphi, u4ehi3]
                              · linarith only [h52, h62, h67, hlam]
                        · linarith only [h62, h7, h8, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                · linarith only [h7, h77, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
                      · linarith only [h0, h81, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h6, h80, h81, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                      · linarith only [h0, h5, h80, h84, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                        · linarith only [h1, h7, h86, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                          · linarith only [h1, h77, h88, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                            · linarith only [h2, h90, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                              · linarith only [h4, h7, h92, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                                · linarith only [h1, h77, h79, h94, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                                  · linarith only [h0, h5, h96, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h79, h80, h96, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
                    · linarith only [h4, h79, h99, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                      · linarith only [h101, h4, h7, h79, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                        · linarith only [h1, h103, h4, h7, h79, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                          · linarith only [h105, h4, h77, h79, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                            · linarith only [h107, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                              · linarith only [h109, h4, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                                · linarith only [h111, h4, h77, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h113 | h113
                                  · linarith only [h0, h113, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                                    · linarith only [h113, h115, h99, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h115, h4, h7, h79, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h118 | h118
              · rcases m.htr 0 3 5 (by decide) (by decide) with h119 | h119
                · linarith only [h119, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                      · linarith only [h0, h123, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h125 | h125
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h126 | h126
                          · linarith only [h1, h119, h126, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h128 | h128
                            · linarith only [h128, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                              · linarith only [h130, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                              · linarith only [h1, h119, h125, h130, hc23, hc35, hlam, hphi]
                        · linarith only [h118, h119, h125, hc13, hc35, hlam, hphi]
                    · linarith only [h122, h5, h6, hc12, hc25, hlam, hphi]
                  · linarith only [h121, h4, h6, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h136 | h136
                · linarith only [h118, h136, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h140 | h140
                      · linarith only [h0, h140, h6, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h142 | h142
                        · linarith only [h1, h118, h142, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h144 | h144
                          · linarith only [h1, h118, h136, h144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h146 | h146
                            · linarith only [h0, h139, h146, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                              · linarith only [h118, h148, h4, h6, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h150 | h150
                                · linarith only [h1, h136, h138, h150, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h152 | h152
                                  · linarith only [h0, h139, h150, h152, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                  · linarith only [h0, h139, h152, h6, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h139, h5, h6, hc12, hc25, hlam, hphi]
                  · linarith only [h138, h4, h6, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h157 | h157
            · linarith only [h157, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h159 | h159
              · linarith only [h159, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h161 | h161
                · linarith only [h161, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h164 | h164
                    · linarith only [h0, h164, h5, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h166 | h166
                      · linarith only [h0, h157, h166, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                        · linarith only [h1, h159, h168, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                          · linarith only [h1, h161, h170, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h172 | h172
                            · linarith only [h172, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                              · linarith only [h159, h163, h164, h172, h174, hc03, hc45, hlam, hphi, ht34]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                                · linarith only [h1, h161, h163, h176, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                                  · linarith only [h163, h164, h172, h174, h178, hc23, hc34, hlam, hphi]
                                  · linarith only [h0, h163, h178, h5, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h163, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h182 | h182
          · rcases m.htr 0 2 5 (by decide) (by decide) with h183 | h183
            · linarith only [h183, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h185 | h185
              · rcases m.htr 0 3 5 (by decide) (by decide) with h186 | h186
                · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
                  · linarith only [h182, h187, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h189 | h189
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                      · linarith only [h0, h183, h190, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                          · linarith only [h1, h193, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h186, h187, h189, h193, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h185, h187, h189, h192, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h182, h183, h189, hc12, hc25, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
                  · linarith only [h182, h198, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                      · linarith only [h0, h201, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                          · linarith only [h1, h186, h204, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h206 | h206
                            · linarith only [h2, h206, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h208 | h208
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                                · linarith only [h1, h186, h198, h200, h208, h209, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                · linarith only [h0, h200, h208, h209, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h200, h208, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h185, h186, h203, hc13, hc35, hlam, hphi]
                    · linarith only [h182, h186, h200, h4, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h182, h185, h4, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h216 | h216
            · linarith only [h182, h216, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h218 | h218
              · rcases m.htr 0 3 5 (by decide) (by decide) with h219 | h219
                · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                  · linarith only [h219, h220, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                    · linarith only [h0, h182, h222, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                      · linarith only [h0, h216, h224, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h226 | h226
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
                          · linarith only [h1, h227, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h219, h226, h227, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                          · linarith only [h218, h226, h230, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
                            · linarith only [h2, h232, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h236 | h236
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h237 | h237
                                    · linarith only [h218, h220, h226, h232, h237, h4, hc12, hc23, hlam, hphi]
                                    · linarith only [h220, h226, h234, h236, h237, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h240 | h240
                                    · linarith only [h0, h182, h236, h240, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h1bigk with h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        rcases p242_3 (m.d 0 1) (by simp) with h244 | h244
                                        · rcases p242_3 (m.d 1 2) (by simp) with h245 | h245
                                          · linarith only [h245, hlam, p242_0]
                                          · rcases p242_3 (m.d 1 3) (by simp) with h247 | h247
                                            · linarith only [h1, h247, hlam]
                                            · linarith only [h220, h247, hlam]
                                        · linarith only [h244, hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        rcases p242_3 (m.d 0 1) (by simp) with h251 | h251
                                        · rcases p242_3 (m.d 1 2) (by simp) with h252 | h252
                                          · linarith only [h0, h252, hlam]
                                          · rcases p242_3 (m.d 1 3) (by simp) with h254 | h254
                                            · linarith only [h254, hlam, p242_0]
                                            · rcases p242_3 (m.d 1 4) (by simp) with h256 | h256
                                              · linarith only [h2, h256, hlam]
                                              · linarith only [h226, h256, hlam]
                                        · linarith only [h251, hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        rcases p242_3 (m.d 0 1) (by simp) with h260 | h260
                                        · rcases p242_3 (m.d 1 2) (by simp) with h261 | h261
                                          · linarith only [h0, h261, hlam]
                                          · rcases p242_3 (m.d 1 3) (by simp) with h263 | h263
                                            · linarith only [h1, h263, hlam]
                                            · rcases p242_3 (m.d 1 4) (by simp) with h265 | h265
                                              · linarith only [h265, hlam, p242_0]
                                              · rcases p242_3 (m.d 1 5) (by simp) with h267 | h267
                                                · linarith only [h267, h3, hlam]
                                                · linarith only [h232, h267, hlam]
                                        · linarith only [h260, hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht0b, ht5b, p242_1, u5ehi1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h0, hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h220, hlam, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h222, hlam, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h224, hlam, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h1, hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h182, h218, h226, hc12, hc24, hlam, hphi, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h226, hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h230, hlam, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h2, hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h182, h2, h236, hc12, hc45, hlam, hphi, ht23, ht34, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h182, h218, h226, h236, hc13, hc45, hlam, hphi, ht34, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h232, hlam, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h3, hlam, p242_0]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h219, h230, h4, hc12, hc23, hlam, hphi, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h219, h220, h230, h4, hc12, hc23, hlam, hphi, p242_1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [h219, h230, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p242_1, u4ehi1]
                                      · have p242_0 := h242c.1
                                        have p242_1 := h242c.2.1
                                        have p242_2 := h242c.2.2.1
                                        have p242_3 := h242c.2.2.2
                                        linarith only [hlam, p242_0]
                                · linarith only [h219, h235, h4, hlam]
                              · linarith only [h218, h219, h230, h234, h4, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                  · linarith only [h0, h294, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h296 | h296
                    · linarith only [h0, h182, h296, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h298 | h298
                      · linarith only [h0, h216, h298, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h300 | h300
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h301 | h301
                          · linarith only [h1, h219, h301, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h303 | h303
                            · linarith only [h2, h303, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h305 | h305
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h306 | h306
                                · linarith only [h218, h219, h306, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h308 | h308
                                  · linarith only [h300, h301, h303, h305, h306, h308, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                                    · linarith only [h1, h300, h308, h310, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                    · linarith only [h1, h300, h306, h310, h4, hc45, hlam, hphi, u4ehi3]
                              · linarith only [h1, h300, h305, h4, hlam]
                        · linarith only [h218, h219, h300, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h315 | h315
                · linarith only [h218, h315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
                  · linarith only [h0, h317, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                    · linarith only [h0, h182, h319, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
                      · linarith only [h0, h216, h321, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h323 | h323
                        · linarith only [h1, h218, h323, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h325 | h325
                          · linarith only [h1, h325, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h327 | h327
                            · linarith only [h2, h327, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h329 | h329
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h330 | h330
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h331 | h331
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                                    · linarith only [h327, h329, h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                                    · linarith only [h0, h218, h329, h331, h332, h4, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h335 | h335
                                    · linarith only [h0, h182, h331, h335, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h1bigk with h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        rcases p337_3 (m.d 0 1) (by simp) with h339 | h339
                                        · rcases p337_3 (m.d 1 2) (by simp) with h340 | h340
                                          · linarith only [h340, hlam, p337_0]
                                          · rcases p337_3 (m.d 1 3) (by simp) with h342 | h342
                                            · linarith only [h1, h342, hlam]
                                            · linarith only [h317, h342, hlam]
                                        · linarith only [h339, hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        rcases p337_3 (m.d 0 1) (by simp) with h346 | h346
                                        · rcases p337_3 (m.d 1 2) (by simp) with h347 | h347
                                          · linarith only [h0, h347, hlam]
                                          · rcases p337_3 (m.d 1 3) (by simp) with h349 | h349
                                            · linarith only [h349, hlam, p337_0]
                                            · rcases p337_3 (m.d 1 4) (by simp) with h351 | h351
                                              · linarith only [h2, h351, hlam]
                                              · linarith only [h323, h351, hlam]
                                        · linarith only [h346, hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        rcases p337_3 (m.d 0 1) (by simp) with h355 | h355
                                        · rcases p337_3 (m.d 1 2) (by simp) with h356 | h356
                                          · linarith only [h0, h356, hlam]
                                          · rcases p337_3 (m.d 1 3) (by simp) with h358 | h358
                                            · linarith only [h1, h358, hlam]
                                            · rcases p337_3 (m.d 1 4) (by simp) with h360 | h360
                                              · linarith only [h360, hlam, p337_0]
                                              · rcases p337_3 (m.d 1 5) (by simp) with h362 | h362
                                                · linarith only [h3, h362, hlam]
                                                · linarith only [h327, h362, hlam]
                                        · linarith only [h355, hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht0b, ht5b, p337_1, u5ehi1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h0, hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h317, hlam, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h319, hlam, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h321, hlam, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h1, hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h1, h218, h329, hc12, hc24, hlam, hphi, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h323, hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h325, hlam, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h2, hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h182, h2, h331, hc12, hc45, hlam, hphi, ht23, ht34, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h2, h218, h329, h331, hc13, hc45, hlam, hphi, ht34, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h327, hlam, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h3, hlam, p337_0]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h3, h315, h330, hc12, hc23, hlam, hphi, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h3, h315, h317, h330, hc12, hc23, hlam, hphi, p337_1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p337_1, u4ehi1]
                                      · have p337_0 := h337c.1
                                        have p337_1 := h337c.2.1
                                        have p337_2 := h337c.2.2.1
                                        have p337_3 := h337c.2.2.2
                                        linarith only [hlam, p337_0]
                                · linarith only [h1, h218, h317, h329, h330, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h388 | h388
                                · linarith only [h329, h388, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h390 | h390
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h391 | h391
                                    · rcases h1bigk with h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        rcases p392_3 (m.d 0 1) (by simp) with h394 | h394
                                        · rcases p392_3 (m.d 1 2) (by simp) with h395 | h395
                                          · linarith only [h395, hlam, p392_0]
                                          · rcases p392_3 (m.d 1 3) (by simp) with h397 | h397
                                            · linarith only [h1, h397, hlam]
                                            · linarith only [h317, h397, hlam]
                                        · linarith only [h394, hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        rcases p392_3 (m.d 0 1) (by simp) with h401 | h401
                                        · rcases p392_3 (m.d 1 2) (by simp) with h402 | h402
                                          · linarith only [h0, h402, hlam]
                                          · rcases p392_3 (m.d 1 3) (by simp) with h404 | h404
                                            · linarith only [h404, hlam, p392_0]
                                            · rcases p392_3 (m.d 1 4) (by simp) with h406 | h406
                                              · linarith only [h2, h406, hlam]
                                              · linarith only [h323, h406, hlam]
                                        · linarith only [h401, hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        rcases p392_3 (m.d 0 1) (by simp) with h410 | h410
                                        · rcases p392_3 (m.d 1 2) (by simp) with h411 | h411
                                          · linarith only [h0, h411, hlam]
                                          · rcases p392_3 (m.d 1 3) (by simp) with h413 | h413
                                            · linarith only [h1, h413, hlam]
                                            · rcases p392_3 (m.d 1 4) (by simp) with h415 | h415
                                              · linarith only [h415, hlam, p392_0]
                                              · rcases p392_3 (m.d 1 5) (by simp) with h417 | h417
                                                · linarith only [h3, h417, hlam]
                                                · linarith only [h327, h417, hlam]
                                        · linarith only [h410, hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht0b, ht5b, p392_1, u5ehi1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h0, hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h317, hlam, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h319, hlam, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h321, hlam, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h1, hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h1, h388, h391, h4, hc12, hc34, hlam, hphi, ht23, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h323, hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h325, hlam, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h2, hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h327, h390, hc12, hc24, hlam, hphi, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h327, h390, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h327, hlam, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h3, hlam, p392_0]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h327, h390, hc12, hc24, hlam, hphi, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h317, h327, h390, hc12, hc24, hlam, hphi, p392_1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [h327, h390, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p392_1, u4ehi1]
                                      · have p392_0 := h392c.1
                                        have p392_1 := h392c.2.1
                                        have p392_2 := h392c.2.2.1
                                        have p392_3 := h392c.2.2.2
                                        linarith only [hlam, p392_0]
                                    · linarith only [h329, h390, h391, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h443 | h443
                                    · linarith only [h0, h329, h390, h4, h443, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h329, h4, h443, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h446 | h446
        · rcases m.htr 0 2 4 (by decide) (by decide) with h447 | h447
          · rcases m.htr 0 2 5 (by decide) (by decide) with h448 | h448
            · linarith only [h0, h3, h448, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h450 | h450
              · rcases m.htr 0 3 5 (by decide) (by decide) with h451 | h451
                · linarith only [h1, h3, h451, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h453 | h453
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h454 | h454
                    · linarith only [h0, h3, h454, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h447, h448, h454, hc12, hc25, hlam, hphi]
                  · linarith only [h446, h448, h453, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h458 | h458
                · linarith only [h0, h3, h447, h450, h458, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h461 | h461
                    · linarith only [h0, h3, h461, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h447, h448, h461, hc12, hc25, hlam, hphi]
                  · linarith only [h446, h448, h460, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h465 | h465
            · linarith only [h2, h3, h447, h465, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h467 | h467
              · linarith only [h446, h447, h467, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h469 | h469
                · linarith only [h2, h3, h446, h447, h469, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h472 | h472
                    · linarith only [h0, h3, h447, h472, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h474 | h474
                      · linarith only [h0, h3, h465, h474, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h476 | h476
                        · linarith only [h1, h3, h467, h474, h476, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h478 | h478
                          · linarith only [h1, h3, h469, h478, hlam]
                          · linarith only [h2, h3, h471, h472, h478, hc23, hc35, hlam, hphi]
                  · linarith only [h446, h447, h471, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h482 | h482
          · rcases m.htr 0 2 5 (by decide) (by decide) with h483 | h483
            · linarith only [h446, h483, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h485 | h485
              · rcases m.htr 0 3 5 (by decide) (by decide) with h486 | h486
                · linarith only [h1, h3, h486, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                  · linarith only [h446, h482, h488, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                    · linarith only [h0, h3, h490, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h446, h482, h490, hc12, hc23, hlam, hphi]
              · linarith only [h446, h482, h485, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h494 | h494
            · linarith only [h482, h494, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h496 | h496
              · rcases m.htr 0 3 5 (by decide) (by decide) with h497 | h497
                · linarith only [h1, h3, h497, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
                  · linarith only [h0, h3, h446, h499, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h501 | h501
                    · linarith only [h0, h3, h501, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
                      · linarith only [h1, h3, h494, h499, h503, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
                        · linarith only [h1, h3, h503, h505, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · linarith only [h496, h497, h499, h505, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h508 | h508
                · linarith only [h2, h3, h496, h508, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
                  · linarith only [h0, h446, h510, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h512 | h512
                    · linarith only [h0, h3, h482, h512, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h514 | h514
                      · linarith only [h0, h446, h514, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                        · linarith only [h1, h496, h516, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h518 | h518
                          · linarith only [h2, h3, h508, h516, h518, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h520 | h520
                            · linarith only [h2, h3, h518, h520, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h2, h3, h520, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h523 | h523
      · linarith only [h2, h523, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h525 | h525
        · rcases m.htr 0 2 4 (by decide) (by decide) with h526 | h526
          · linarith only [h0, h2, h526, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h528 | h528
            · linarith only [h0, h2, h528, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h530 | h530
              · linarith only [h1, h2, h530, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h532 | h532
                · linarith only [h0, h2, h525, h532, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h535 | h535
                    · linarith only [h0, h2, h526, h535, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h537 | h537
                      · linarith only [h0, h523, h528, h537, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h539 | h539
                        · linarith only [h0, h2, h530, h534, h539, hlam]
                        · linarith only [h0, h2, h534, h539, hc23, hc34, hlam, hphi]
                  · linarith only [h525, h526, h534, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h543 | h543
          · linarith only [h0, h2, h543, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h545 | h545
            · linarith only [h1, h523, h525, h545, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h547 | h547
              · linarith only [h1, h2, h547, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h549 | h549
                · linarith only [h547, h549, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h551 | h551
                  · linarith only [h0, h523, h525, h551, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h553 | h553
                    · linarith only [h0, h2, h543, h553, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h555 | h555
                      · linarith only [h1, h523, h545, h551, h555, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h557 | h557
                        · linarith only [h1, h2, h547, h553, h557, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h559 | h559
                          · linarith only [h1, h523, h549, h559, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h561 | h561
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h562 | h562
                              · linarith only [h1, h523, h551, h557, h561, h562, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h564 | h564
                                · linarith only [h562, h564, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h566 | h566
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h567 | h567
                                    · rcases h1bigk with h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h2, h553, hc12, hc24, hlam, hphi, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h2, h551, h553, hc12, hc24, hlam, hphi, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h2, hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h523, hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h0, hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h551, hlam, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h553, hlam, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h555, hlam, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h1, hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h1, h2, h553, hc12, hc24, hlam, hphi, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h557, hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h559, hlam, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h0, h553, hc12, hc24, hlam, hphi, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        rcases p568_3 (m.d 0 1) (by simp) with h585 | h585
                                        · linarith only [h2, h585, hlam]
                                        · linarith only [h0, h585, hlam]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        rcases p568_3 (m.d 0 1) (by simp) with h588 | h588
                                        · linarith only [h2, h588, hlam]
                                        · linarith only [h1, h588, hlam]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h1, h523, h551, h553, h562, hc12, hc34, hlam, hphi, ht23, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h1, h551, h555, h562, h566, hc12, hc34, hlam, hphi, ht23, p568_1]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        rcases p568_3 (m.d 0 1) (by simp) with h594 | h594
                                        · linarith only [h523, h594, hlam]
                                        · linarith only [h0, h594, hlam]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        rcases p568_3 (m.d 0 1) (by simp) with h597 | h597
                                        · linarith only [h523, h597, hlam]
                                        · linarith only [h1, h597, hlam]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [h561, hlam, p568_0]
                                      · have p568_0 := h568c.1
                                        have p568_1 := h568c.2.1
                                        have p568_2 := h568c.2.2.1
                                        have p568_3 := h568c.2.2.2
                                        linarith only [hlam, p568_0]
                                    · linarith only [h1, h2, h551, h553, h562, h567, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h553, h561, h566, hlam]
                            · linarith only [h1, h2, h551, h561, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h605 | h605
    · rcases m.htr 0 1 5 (by decide) (by decide) with h606 | h606
      · linarith only [h1, h606, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h608 | h608
        · linarith only [h0, h1, h608, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h610 | h610
          · rcases m.htr 0 2 5 (by decide) (by decide) with h611 | h611
            · linarith only [h0, h1, h611, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h613 | h613
              · rcases m.htr 0 3 5 (by decide) (by decide) with h614 | h614
                · rcases m.htr 1 2 3 (by decide) (by decide) with h615 | h615
                  · linarith only [h0, h1, h608, h615, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h617 | h617
                    · linarith only [h0, h1, h615, h617, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h610, h611, h617, hc12, hc25, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
                  · linarith only [h0, h1, h614, h620, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h622 | h622
                    · linarith only [h0, h1, h614, h622, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1, h610, h614, h622, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1, h605, h613, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h626 | h626
            · linarith only [h1, h605, h610, h626, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h628 | h628
              · rcases m.htr 0 3 5 (by decide) (by decide) with h629 | h629
                · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
                  · linarith only [h0, h1, h608, h630, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h632 | h632
                    · linarith only [h0, h1, h610, h630, h632, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h634 | h634
                      · linarith only [h605, h606, h626, h632, h634, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h636 | h636
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h637 | h637
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h638 | h638
                            · linarith only [h605, h606, h630, h637, h638, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h605, h606, h638, hc45, hlam, hphi, u4ehi1]
                          · linarith only [h1, h605, h629, h636, h637, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h1, h605, h636, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
                  · linarith only [h0, h1, h629, h643, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h645 | h645
                    · linarith only [h0, h610, h645, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h647 | h647
                      · linarith only [h1, h605, h629, h645, h647, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h649 | h649
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h650 | h650
                          · linarith only [h1, h605, h629, h650, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                          · linarith only [h1, h605, h649, h650, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                        · linarith only [h1, h605, h645, h649, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h605, h628, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h655 | h655
      · linarith only [h1, h655, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h657 | h657
        · linarith only [h0, h1, h657, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h659 | h659
          · linarith only [h0, h605, h659, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h661 | h661
            · linarith only [h0, h1, h661, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h663 | h663
              · rcases m.htr 0 3 5 (by decide) (by decide) with h664 | h664
                · rcases m.htr 1 2 3 (by decide) (by decide) with h665 | h665
                  · linarith only [h0, h1, h657, h665, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h667 | h667
                    · linarith only [h0, h605, h659, h667, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h669 | h669
                      · linarith only [h0, h655, h661, h669, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h671 | h671
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h672 | h672
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h673 | h673
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h674 | h674
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h675 | h675
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h676 | h676
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h677 | h677
                                    · linarith only [h663, h677, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · rcases h1bigk with h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h655, h665, h671, h673, hc12, hc23, hlam, hphi, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h1, hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h605, hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h655, hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h0, hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h665, hlam, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h667, hlam, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h669, hlam, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h0, h665, hc12, hc23, hlam, hphi, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        rcases p679_3 (m.d 0 1) (by simp) with h691 | h691
                                        · linarith only [h1, h691, hlam]
                                        · linarith only [h0, h691, hlam]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h665, h673, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p679_1, u5ehi1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h0, h655, h665, hc12, hc23, hlam, hphi, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h0, h667, hc12, hc24, hlam, hphi, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        rcases p679_3 (m.d 0 1) (by simp) with h698 | h698
                                        · linarith only [h605, h698, hlam]
                                        · linarith only [h0, h698, hlam]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h671, hlam, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h0, h655, h665, h671, hc12, hc23, hlam, hphi, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h0, h669, hc12, hc25, hlam, hphi, p679_1]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        rcases p679_3 (m.d 0 1) (by simp) with h705 | h705
                                        · linarith only [h655, h705, hlam]
                                        · linarith only [h0, h705, hlam]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h672, hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [h673, hlam, p679_0]
                                      · have p679_0 := h679c.1
                                        have p679_1 := h679c.2.1
                                        have p679_2 := h679c.2.2.1
                                        have p679_3 := h679c.2.2.2
                                        linarith only [hlam, p679_0]
                                  · linarith only [h0, h605, h667, h676, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h1, h665, h675, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h664, h665, h674, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · linarith only [h0, h605, h673, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h664, h672, hlam]
                        · linarith only [h1, h663, h664, h671, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h717 | h717
                  · linarith only [h0, h1, h664, h717, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h719 | h719
                    · linarith only [h0, h605, h663, h664, h719, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h721 | h721
                      · linarith only [h0, h721, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h723 | h723
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h724 | h724
                          · linarith only [h663, h664, h724, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h0, h1, h724, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h663, h723, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h728 | h728
                · linarith only [h663, h728, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
                  · linarith only [h0, h1, h663, h730, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h732 | h732
                    · linarith only [h0, h1, h663, h732, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h734 | h734
                      · linarith only [h0, h1, h663, h734, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h736 | h736
                        · linarith only [h0, h1, h663, h730, h736, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h736, hc12, hc34, hlam, hphi, ht23]

end R2N4
